{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ImportQualifiedPost #-}

import Kore.Parser
import Kore.Unparser
import Kore.Validate.DefinitionVerifier
import Kore.Builtin qualified as Builtin
import Kore.Verified qualified as Verified
import Kore.Syntax.Module
import Kore.IndexedModule.IndexedModule
import Kore.Attribute.Symbol (Symbol)
import Kore.Attribute.Attributes
import Kore.Syntax.Application (SymbolOrAlias (..))
import Kore.Syntax.Definition (definitionAttributes)
import Kore.Syntax.Id (Id(..), AstLocation(..))

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


transformDefinition :: ParsedDefinition -> ParsedDefinition
transformDefinition d = d

getCfgSort :: ParsedDefinition -> AttributePattern
getCfgSort d =
    let da = getAttributes (definitionAttributes d) in
        attributePattern (SymbolOrAlias (Id (Data.Text.pack "topCellInitializer") AstLocationNone) []) da


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
        _
            -> usage