module Runner

import Data.Fuel
import Data.List.Lazy

import Test.DepTyCheck.Gen

import Test.Verilog.Gen
import Test.Verilog.Pretty

import Text.PrettyPrint.Bernardy

import System.Random.Pure.StdGen

%default total

StdModules : ModuleSigsList
StdModules =
  [ MkModuleSig 2 1
  , MkModuleSig 2 1
  , MkModuleSig 2 1
  , MkModuleSig 2 1
  , MkModuleSig 1 1
  ]

StdModulesNames : Vect StdModules .length String
StdModulesNames =
  [ "and"
  , "or"
  , "nand"
  , "xor"
  , "not"
  ]

PrettyOpts : LayoutOpts
PrettyOpts = Opts 152

main : IO ()
main = do
  let vals = unGenTryN 10 someStdGen $ genModules (limit 4) StdModules
  Lazy.for_ vals $ \val => do
    putStrLn "-------------------\n"
    putStr $ render PrettyOpts $ prettyModules StdModulesNames val
