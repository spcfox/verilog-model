module Test.Verilog

import Data.List
import Data.Vect
import Data.Vect.Quantifiers

%default total

-- There may be a phantom type of submodules representing an outer world.
-- It has the same rules for connections, must be present in any composite module and only once.

-- Submodules can be indices to some outer contexts, to split description of a submodule and its instantiation

data Module : (ins, outs : Nat) -> (unsatOuts : List ?out_of_subm) -> Type where
  Not   : Module 1 1 []
  And   : Module 1 2 []
  Or    : Module 1 2 []
  Nand  : Module 1 2 []

  Empty   : Module is os (replicate os ?each_output_is_unsatisfied)
  NewSub  : (base : Module is os uos) -> (submodule : Module subIs subOs []) -> Module is os (?sub'sOuts::uos)
  NewConn : (base : Module is os (uo::uos)) -> (conn : ?conn_satifsying_uo) -> Module is os ous

  -- maybe, this type have to be indexed by a list of submodules

namespace AlternativeIdea

  data Module : (ins, outs : Nat) -> Type where
    Not   : Module 1 1
    And   : Module 1 2
    Or    : Module 1 2
    Nand  : Module 1 2

    Composite : (subs : Vect subsCnt (ins ** outs ** Module ins outs)) ->
                (connections : All (\(is ** _ ** _) => Vect is ?an_appropriate_output_of_some_submodule) subs) ->
                Module is os
