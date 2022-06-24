{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE DerivingStrategies #-}

import Kore.Parser
import Kore.Unparser
import Kore.Validate.DefinitionVerifier
import Kore.Builtin qualified as Builtin
import Kore.Verified qualified as Verified
import Kore.Syntax.Module
import Kore.IndexedModule.IndexedModule
import Kore.Attribute.Symbol (Symbol)
import Kore.Attribute.Attributes
import Kore.Internal.Predicate (Predicate, fromPredicate)
import Control.Comonad.Trans.Cofree (Cofree, unwrap)
import Kore.Syntax.Pattern (Pattern(..))
import Kore.Syntax.Application (Application (..), SymbolOrAlias (..))
import Kore.Syntax.Definition (definitionAttributes)
import Kore.Syntax.Id (Id(..), AstLocation(..))

import System.Console.Haskeline (
    InputT,
    getInputLine,
    defaultSettings,
    outputStrLn,
    runInputT,
 )

import System.Environment (getArgs, getProgName)
import Data.Text ( Text, pack )
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Pretty (
    Doc,
    hPutDoc,
    putDoc,
    renderString
 )
import Data.Text.IO
import System.IO (
    IOMode (WriteMode),
    withFile,
 )

data CRLPattern variable annotation = CRLPattern
    { crlplist :: [Pattern variable annotation]
    , crlpside :: Predicate variable
    }
    deriving stock (Show)


{-}
instance (Unparse variable, Unparse annotation) => Unparse (CRLPattern variable annotation) where
    unparse (CRLPattern l s) = unparse (fromPredicate s)
-}
crlArity :: CRLPattern variable annotation -> Int
crlArity = length . crlplist

transformDefinition :: ParsedDefinition -> ParsedDefinition
transformDefinition d = d

{- getCfgSort :: ParsedDefinition -> AttributePattern -}
getCfgSort d =
    let da = getAttributes (definitionAttributes d) in
        let ap = attributePattern (SymbolOrAlias (Id (Data.Text.pack "topCellInitializer") AstLocationNone) []) da in
            ap


withDefinition :: String -> (ParsedDefinition -> IO ()) -> IO ()
withDefinition inputFileName action = do
    contents <- Data.Text.IO.readFile inputFileName
    let esParsedDefinition = Kore.Parser.parseKoreDefinition inputFileName contents
    case esParsedDefinition of
        Left s
            -> do
                Prelude.putStrLn $ "cannot parse: " ++ s
        Right parsedDefinition
            -> action parsedDefinition

withVerifiedDefinition :: String -> (ParsedDefinition -> (Map.Map ModuleName (VerifiedModule Kore.Attribute.Symbol.Symbol)) -> IO ()) -> IO ()
withVerifiedDefinition inputFileName action =
    withDefinition inputFileName $ \parsedDefinition ->
        do
            let result = verifyAndIndexDefinition Builtin.koreVerifiers parsedDefinition
            case result of
                Left err -> 
                    Prelude.putStrLn $ "verification of kore failed"
                Right mmap ->
                    action parsedDefinition mmap

transformDefinitionFile :: String -> String -> IO ()
transformDefinitionFile inputFileName outputFileName =
    withDefinition inputFileName $ \parsedDefinition ->
        do
            let transformed = transformDefinition parsedDefinition
            let unparsedDefinition = unparse transformed
            System.IO.withFile outputFileName WriteMode $ \outputFileHandle ->
                Pretty.hPutDoc outputFileHandle unparsedDefinition


printCfgSort :: [String] -> IO ()
printCfgSort args =
    case args of
        [inputFileName]
            ->
                withDefinition inputFileName $ \parsedDefinition ->
                    do
                        let cfgSort = getCfgSort parsedDefinition
                        let unparsed = unparse cfgSort
                        Pretty.putDoc $ (unparsed)

usage :: IO ()
usage = do
    name <- System.Environment.getProgName
    Prelude.putStrLn $ "Usage: " ++ name ++ " transform inputFileName outputFileName"

transform :: [String] -> IO ()
transform args = 
    case args of
        [inputFileName, outputFileName] 
            -> do
                Prelude.putStrLn $ "input: " ++ inputFileName ++ ", output: " ++ outputFileName
                transformDefinitionFile inputFileName outputFileName


validate :: [String] -> IO ()
validate args =
    case args of
        [inputFileName]
            -> withVerifiedDefinition inputFileName $ \parsedDefinition verifiedDefinition ->
                do
                    Prelude.putStrLn $ "Kore file verified"

repl :: [String] -> IO ()
repl args = runInputT defaultSettings loop
   where
       loop :: InputT IO ()
       loop = do
           minput <- getInputLine "% "
           case minput of
               Nothing -> return ()
               Just "quit" -> return ()
               Just input -> do outputStrLn $ "Input was: " ++ input
                                loop

main :: IO ()
main = do
    args <- System.Environment.getArgs
    case args of
        "transform":args
            -> transform args
        "validate":args
            -> validate args
        "print-cfg-sort":args
            -> printCfgSort args
        "repl":args
            -> repl args
        _
            -> usage