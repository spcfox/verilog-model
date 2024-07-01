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

(++) : SVect a -> SVect b -> SVect (a + b)
(++) [] xs = xs
(++) (x :: xs) ys = x :: (xs ++ ys)

(.length) : SVect l -> Nat
(.length) [] = Z
(.length) (x :: xs) = S (xs .length)

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

genPlusOneName : {l : Nat} -> Fuel -> (names: SVect l) -> (un: UniqNames l names) -> Gen MaybeEmpty (out : String ** UniqNames (S l) (out :: names))
genPlusOneName x names un = do 
  (name ** uname) <- rawNewName x @{namesGen'} l names un
  pure (name ** Cons names name un uname)

genNExtraNames : {l : Nat} -> Fuel -> (n : Nat) -> (names: SVect l) -> (un: UniqNames l names) -> 
  Gen MaybeEmpty (newNames : SVect (n + l) ** UniqNames (n + l) newNames)
genNExtraNames _ Z names un = pure (names ** un)
genNExtraNames x (S k) names un = do
  (tail ** utail) <- genNExtraNames x k names un
  (head ** uhead) <- genPlusOneName x tail utail
  pure (head :: tail ** uhead)

toVect : SVect l -> Vect l String
toVect [] = []
toVect (x :: xs) = x :: toVect xs

public export
fromVect : Vect l String -> SVect l
fromVect [] = []
fromVect (x :: xs) = x :: fromVect xs

invertConn' : Vect l (Fin outs, Fin ins) -> Vect ins (List (Fin outs)) -> Vect ins (List (Fin outs))
invertConn' [] ys = ys
invertConn' ((outIdx, inIdx):: xs) ys = invertConn' xs $ updateAt inIdx (outIdx ::) ys

invertConn : {ins: Nat} -> Vect outs (Fin ins) -> Vect ins (List (Fin outs))
invertConn xs = invertConn' (withIndex xs) (replicate ins [])

pf : LTE (S x) y -> LTE x y
pf (LTESucc LTEZero) = LTEZero
pf (LTESucc (LTESucc z)) = LTESucc $ pf $ LTESucc z

getFirstTopLevel : {realOutputs: Nat} -> List (Fin (plus realOutputs subMInputs)) -> Maybe (Fin realOutputs)
getFirstTopLevel [] = Nothing
getFirstTopLevel (x :: xs) = case isLT (finToNat x) realOutputs of
  Yes a => Just $ natToFinLT (finToNat x)
  No b => getFirstTopLevel xs

findNoTopLevel : {realOutputs: Nat} -> Vect l (Fin (plus realInputs subMOutputs), List (Fin (plus realOutputs subMInputs))) 
                                    -> List (Fin (plus realInputs subMOutputs))
findNoTopLevel xs = (foldl (\acc, (i,r) => case getFirstTopLevel r of
  Just n => acc
  Nothing => i :: acc) [] xs)

genInternalLookupTable : (internals : List (Fin l)) -> (names: Vect (internals.length) String) -> SortedMap (Fin l) String
genInternalLookupTable [] [] = empty
genInternalLookupTable (x :: xs) (y :: ys) = insert x y $ genInternalLookupTable xs ys

genInputNames' : {realInputs: Nat} -> {realOutputs: Nat} -> Vect realOutputs String 
                                                         -> SortedMap (Fin (plus realInputs subMOutputs)) String 
                                                         -> Vect l (Fin (plus realInputs subMOutputs), 
                                                                   List (Fin (plus realOutputs subMInputs))) 
                                                         -> Vect l String
genInputNames' oNames lut [] = []
genInputNames' oNames lut ((i, v) :: xs) = (case getFirstTopLevel v of
  Just x => index x oNames
  Nothing => case lookup i lut of
    Just x => x
    Nothing => "<error>") :: genInputNames' oNames lut xs

genInputNames : {realInputs: Nat} -> {realOutputs: Nat} -> Vect realInputs String -> Vect realOutputs String 
                                                        -> SortedMap (Fin (plus realInputs subMOutputs)) String 
                                                        -> Vect (plus realInputs subMOutputs) 
                                                                (Fin (plus realInputs subMOutputs), List (Fin (plus realOutputs subMInputs))) 
                                                        -> Vect (plus realInputs subMOutputs) String
genInputNames iNames oNames lut xs = do
  let (first, second) = splitAt realInputs xs
  iNames ++ genInputNames' oNames lut second

genOutputNames' : Vect inputs String -> Vect l (Fin inputs) -> Vect l String
genOutputNames' inputNames [] = []
genOutputNames' inputNames (x :: xs) = index x inputNames :: genOutputNames' inputNames xs

genOutputNames : {realOutputs: Nat} -> Vect inputs String -> Vect realOutputs String 
                                    -> Vect (plus realOutputs subMInputs) (Fin inputs) 
                                    -> Vect (plus realOutputs subMInputs) String
genOutputNames iNames oNames xs = do
  let (first, second) = splitAt realOutputs xs
  oNames ++ genOutputNames' iNames second


genAssigns' : {realOutputs: Nat} -> Vect inputs String -> Vect realOutputs String 
                                 -> Vect l (Fin realOutputs, Fin inputs) -> List (Fin realOutputs, Fin inputs) 
genAssigns' iNames oNames xs = filter (\(outId, inId) => (index outId oNames) /= (index inId iNames)) (toList xs)

genAssigns :  {realOutputs: Nat} -> Vect inputs String -> Vect realOutputs String 
                                 -> Vect (plus realOutputs subMInputs) (Fin inputs) -> List (Fin realOutputs, Fin inputs)
genAssigns iNames oNames xs = do
  let (first, second) = splitAt realOutputs xs
  genAssigns' iNames oNames $ withIndex first

export
prettyModules : {opts : _} -> {ms : _} -> Fuel -> (names : SVect ms.length) -> UniqNames ms.length names => Modules ms -> Gen0 $ Doc opts
prettyModules x _ End = pure empty
prettyModules x names @{un} (NewCompositeModule m subMs conn cont) = do
  (name ** isnew) <- rawNewName x @{namesGen'} ms.length names un
  recur <- prettyModules x (name::names) cont
  (namesWithInput ** uni) <- genNExtraNames x m.inputs names un
  let inputNames = take m.inputs $ toVect namesWithInput
  (namesWithIO ** unio) <- genNExtraNames x m.outputs namesWithInput uni
  let outputNames = take m.outputs $ toVect namesWithIO
  (namesIOWithSubMs ** uniosub) <- genNExtraNames x subMs.length namesWithIO unio
  let subMInstanceNames = take subMs.length $ toVect namesIOWithSubMs
  let outerModuleInputs = map ("input logic " ++) inputNames
  let outerModuleOutputs = map ("output logic " ++) outputNames 
  let outerModuleIO = toList $ line <$> (outerModuleOutputs ++ outerModuleInputs)
  let outputToDriver = connFwdRel $ conn
  let inputToDriven : Vect (plus (m .inputs) (totalOutputs subMs)) (List (Fin (plus (m .outputs) (totalInputs subMs)))) = invertConn outputToDriver
  let noTLDrivenInputs = findNoTopLevel $ withIndex inputToDriven
  (namesWithInternal ** unint) <- genNExtraNames x noTLDrivenInputs.length namesIOWithSubMs uniosub
  let internalNames = take noTLDrivenInputs.length $ toVect namesWithInternal
  let internalLUT = genInternalLookupTable noTLDrivenInputs internalNames
  let fullInputNames : Vect (plus (m .inputs) (totalOutputs subMs)) String 
                      = genInputNames inputNames outputNames internalLUT $ withIndex inputToDriven
  let (_, subMONames) = splitAt (m .inputs) fullInputNames
  let fullOutputNames : Vect (plus (m .outputs) (totalInputs subMs)) String 
                      = genOutputNames fullInputNames outputNames outputToDriver
  let (_, subMINames) = splitAt (m .outputs) fullOutputNames
  let assigns = genAssigns fullInputNames outputNames outputToDriver
  pure $ vsep
    [ enclose (flush $ line "module" <++> line name) (line "endmodule:" <++> line name) $ flush $ indent 2 $ vsep $ 
      [ tuple outerModuleIO <+> symbol ';' , line "" ] ++
        (zip (toList subMInstanceNames) (withIndex subMs.asList) <&> \(instanceName, subMsIdx, msIdx) =>
          line (index msIdx $ toVect names) <++> line instanceName <+> do
            let inputs  = List.allFins (index ms $ index' subMs.asList subMsIdx).inputs  <&> toTotalInputsIdx subMsIdx
            let outputs = List.allFins (index ms $ index' subMs.asList subMsIdx).outputs <&> toTotalOutputsIdx subMsIdx

            let inputs  = inputs  <&> flip index subMINames
            let outputs = outputs <&> flip index subMONames

            tuple $ line <$> outputs ++ inputs
        ) ++ [line ""] ++ (assigns <&> \(outIdx, inIdx) =>
          line "assign" <++> line (index outIdx outputNames) <++> symbol '=' <++> line (index inIdx fullInputNames) <+> symbol ';'
        )
    , line ""
    , recur
    ]