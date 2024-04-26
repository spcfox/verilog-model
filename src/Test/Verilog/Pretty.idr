module Test.Verilog.Pretty

import Data.Vect

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

withIndex : (xs : List a) -> List (Fin $ length xs, a)
withIndex []      = []
withIndex (x::xs) = (FZ, x) :: map (mapFst FS) (withIndex xs)

export
prettyModules : {opts : _} -> {ms : _} -> (names : Vect ms.length String) -> Modules ms -> Doc opts
prettyModules _ End = empty
prettyModules names (NewCompositeModule m subMs conn cont) = do
  let name = newName names
  vsep
    [ enclose (line "module" <++> line name) (line "endmodule:" <++> line name) $ indent 2 $ vsep $
        [ tuple ?outputs_and_inputs <+> symbol ';' ] ++
          (withIndex (FinsList.toList subMs) <&> \(subMsIdx, msIdx) =>
            enclose (line (index msIdx names) <++> line "g" <+> line (show subMsIdx)) (symbol ';') $
              tuple ?foo
          )
    , prettyModules (name::names) cont
    ]
