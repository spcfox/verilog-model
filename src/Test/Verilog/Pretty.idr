module Test.Verilog.Pretty

import Data.Either
import Data.List
import Data.List.Extra
import Data.List1
import Data.List.Lazy

import Data.Fin.Split
import Data.Fuel
import Data.SortedMap
import public Data.Vect
import Data.Vect.Extra

import public Test.Verilog

import Test.DepTyCheck.Gen
import System.Random.Pure.StdGen

import Text.PrettyPrint.Bernardy

import Syntax.IHateParens.List
import Syntax.IHateParens.SortedMap

%default total

-- NOTICE: currently we are pretty printing modules deterministically.
-- We are going to add variability to the printing in the future (say,
-- inlining of composites and other synonimical representations of the same abstract model).

toTotalInputsIdx : {ms : _} -> {subMs : FinsList ms.length} ->
                   (idx : Fin subMs.asList.length) ->
                   Fin (index ms (index' subMs.asList idx)).inputs ->
                   Fin $ totalInputs {ms} subMs
toTotalInputsIdx {subMs=i::_ } FZ       x = indexSum $ Left x
toTotalInputsIdx {subMs=i::is} (FS idx) x = indexSum $ Right $ toTotalInputsIdx idx x

toTotalOutputsIdx : {ms : _} -> {subMs : FinsList ms.length} ->
                    (idx : Fin subMs.asList.length) ->
                    Fin (index ms $ index' subMs.asList idx).outputs ->
                    Fin $ totalOutputs {ms} subMs
toTotalOutputsIdx {subMs=i::_ } FZ       x = indexSum $ Left x
toTotalOutputsIdx {subMs=i::is} (FS idx) x = indexSum $ Right $ toTotalOutputsIdx idx x

connName : Fin (m.inputs + totalOutputs {ms} subMs) -> String
connName n = "c\{show n}"

outputName : Fin (m.outputs + totalInputs {ms} subMs) -> String
outputName n = "o\{show n}"

isModuleInput : {m : _} -> Fin (m.inputs + totalOutputs {ms} subMs) -> Bool
isModuleInput = isLeft . splitSum

isModuleOutput : {m : _} -> Fin (m.outputs + totalInputs {ms} subMs) -> Bool
isModuleOutput = isLeft . splitSum

connFwdRel : Connections f t -> Vect t $ Fin f
connFwdRel []      = []
connFwdRel (i::cs) = i :: connFwdRel cs

public export
data SVect : (len : Nat) -> Type where
  ||| Empty vector
  Nil  : SVect Z
  ||| A non-empty vector of length `S len`, consisting of a head element and
  ||| the rest of the list, of length `len`.
  (::) : (x : String) -> (xs : SVect len) -> SVect (S len)

public export
data UniqNames : (l : Nat) -> SVect l -> Type
public export
data NameIsNew : (l : Nat) -> (names: SVect l) -> String -> UniqNames l names -> Type

-- Port JustNew
public export
data UniqNames : (l : Nat) -> SVect l -> Type where
  Empty : UniqNames 0 []
  JustNew : {l : Nat} -> (names : SVect l) -> (name: String) -> (un: UniqNames l names) -> NameIsNew l names name un -> UniqNames l names
  Cons : {l : Nat} -> (names : SVect l) -> (name: String) -> (un: UniqNames l names) -> NameIsNew l names name un -> UniqNames (S l) (name :: names)

public export
data NameIsNew : (l : Nat) -> (names: SVect l) -> (name: String) -> UniqNames l names -> Type where
  NNEmpty : NameIsNew 0 [] s Empty
  NNCons : (0 _ : So $ x /= name) -> (nin: NameIsNew l xs x nn) -> NameIsNew (S l) (x :: xs) name (Cons xs x nn nin)

-- Minimize the signature while preserving the issue.
export
rawNewName : Fuel -> (Fuel -> Gen MaybeEmpty String) =>
             (l : Nat) -> (names: SVect l) -> (un: UniqNames l names) -> Gen MaybeEmpty (s ** NameIsNew l names s un)

namesGen : Gen0 String
namesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

namesGen' : Fuel -> Gen MaybeEmpty String
namesGen' _ = namesGen

toVect : SVect l -> Vect l String
toVect [] = []
toVect (x :: xs) = x :: toVect xs

public export
fromVect : Vect l String -> SVect l
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

export
prettyModules : {opts : _} -> {ms : _} -> Fuel -> (names : SVect ms.length) -> UniqNames ms.length names => Modules ms -> Gen0 $ Doc opts
prettyModules x _ End = pure empty
prettyModules x names @{un} (NewCompositeModule m subMs conn cont) = do
  (name ** isnew) <- rawNewName x @{namesGen'} ms.length names un
  recur <- prettyModules x (name::names) cont
  let names = toVect names
  pure $ do
    let rawFwdRel : Vect (m.outputs + totalInputs {ms} subMs) $ Fin $ m.inputs + totalOutputs {ms} subMs := connFwdRel conn
    let backRel = reverseMapping rawFwdRel
    let DirectAss : Type
        DirectAss = SortedMap (Fin $ m.outputs + totalInputs {ms} subMs) (Fin $ m.inputs + totalOutputs {ms} subMs)
    let directAssModuleIn, directAssOuts : DirectAss
        directAssModuleIn = fromList $ mapMaybe id $ Prelude.toList $ flip mapI rawFwdRel $ \idxO, idxI =>
                              if isModuleInput idxI && isModuleOutput idxO then Just (idxO, idxI) else Nothing
        directAssOuts = fromList $ SortedMap.toList backRel >>= \(o, is) => tail is <&> (, o) -- we can assign both to `o`, or to `head is`
        directAss := directAssModuleIn `mergeLeft` directAssOuts
    let fwdRel : Vect (m.outputs + totalInputs {ms} subMs) String := rawFwdRel `zip` withIndex (fromMap directAss) <&> \(conn, out, directIn) =>
                  maybe (connName conn) (const $ outputName out) directIn
    vsep
      [ enclose (flush $ line "module" <++> line name) (line "endmodule:" <++> line name) $ flush $ indent 2 $ vsep $ do
          let outerModuleInputs  = List.allFins m.inputs  <&> ("input logic " ++) . connName {subMs}  . indexSum . Left
          let outerModuleOutputs = List.allFins m.outputs <&> ("output logic " ++) . flip index fwdRel . indexSum . Left
          let outerModuleIO = line <$> outerModuleOutputs ++ outerModuleInputs
          [ tuple outerModuleIO <+> symbol ';' , line "" ] ++
            (withIndex subMs.asList <&> \(subMsIdx, msIdx) =>
              enclose (line (index msIdx names) <++> line "g" <+> line (show subMsIdx)) (flush $ symbol ';') $ do
                let inputs  = List.allFins (index ms $ index' subMs.asList subMsIdx).inputs  <&> toTotalInputsIdx subMsIdx
                let outputs = List.allFins (index ms $ index' subMs.asList subMsIdx).outputs <&> toTotalOutputsIdx subMsIdx

                let inputs  = inputs  <&> flip index fwdRel . indexSum . Right
                let outputs = outputs <&> connName {m}      . indexSum . Right

                tuple $ line <$> outputs ++ inputs
            ) ++
            (directAss.asList <&> \(o, i) => "assign" <++> line (outputName o) <++> "=" <++> line (connName i) <+> ";"
            )
      , line ""
      , recur
      ]
