module Runner

import Data.Fuel
import Data.List.Lazy

import Test.DepTyCheck.Gen

import Test.Verilog.Gen
import Test.Verilog.Pretty
import Test.Verilog.Pretty.Derived

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

StdModuleNamesS : SVect StdModules .length
StdModuleNamesS =
  [ "and"
  , "or"
  , "nand"
  , "xor"
  , "not"
  ]

PrettyOpts : LayoutOpts
PrettyOpts = Opts 152

-- namesGen : Gen0 String
-- namesGen = pack <$> listOf {length = choose (1,10)} (choose ('a', 'z'))

-- namesGen' : Fuel -> Gen MaybeEmpty String
-- namesGen' _ = namesGen

main : IO ()
main = do
  -- let deb = unGenTryN 1 someStdGen $ rawNewName (limit 10) @{namesGen'} 3 ["a", "b", "c"] testUniq
  -- Lazy.for_ deb $ \(s ** _) => do
  --   putStrLn s
  let vals = unGenTryN 10 someStdGen $ genModules (limit 4) StdModules >>= mypprint (limit 10) StdModuleNamesS %search
  Lazy.for_ vals $ \val => do
    putStrLn "-------------------\n"
    putStr $ render PrettyOpts $ val
