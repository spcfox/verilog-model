module Test.Verilog.Pretty

import Data.Either
import Data.List
import Data.List1
import Data.SortedMap
import public Data.Vect

import Deriving.DepTyCheck.Util.Collections -- I wish it was a separate library

import public Test.Verilog

import Text.PrettyPrint.Bernardy

%default total

-- NOTICE: currently we are pretty printing modules deterministically.
-- We are going to add variability to the printing in the future (say,
-- inlining of composites and other synonimical representations of the same abstract model).

newName : Vect n String -> String
newName existing = assert_total go 0 where
  covering
  go : Nat -> String
  go n = do
    let curr = "module\{show n}"
    if isJust $ find (== curr) existing then go (S n) else curr

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

export
prettyModules : {opts : _} -> {ms : _} -> (names : Vect ms.length String) -> Modules ms -> Doc opts
prettyModules _ End = empty
prettyModules names (NewCompositeModule m subMs conn cont) = do
  let name = newName names
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
    , prettyModules (name::names) cont
    ]
