module Test.Verilog.Pretty

import Data.Fin.Extra
import Data.List
import public Data.Vect

import public Test.Verilog

import Text.PrettyPrint.Bernardy

%default total

%inline
(.length) : List a -> Nat
(.length) = length

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

withIndex : (xs : List a) -> List (Fin $ length xs, a)
withIndex []      = []
withIndex (x::xs) = (FZ, x) :: map (mapFst FS) (withIndex xs)

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

connFwdRel : Connections f t -> Vect t $ Fin f
connFwdRel []      = []
connFwdRel (i::cs) = i :: connFwdRel cs

export
prettyModules : {opts : _} -> {ms : _} -> (names : Vect ms.length String) -> Modules ms -> Doc opts
prettyModules _ End = empty
prettyModules names (NewCompositeModule m subMs conn cont) = do
  let name = newName names
  let fwdRel : Vect (m.outputs + totalInputs {ms} subMs) $ Fin $ m.inputs + totalOutputs {ms} subMs := connFwdRel conn
  let fwdRel : Vect (m.outputs + totalInputs {ms} subMs) String := map connName fwdRel
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
          )
    , line ""
    , prettyModules (name::names) cont
    ]
