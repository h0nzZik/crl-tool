{-# LANGUAGE TemplateHaskell #-}
import Kore.Parser
import Kore.Unparser
import Kore.Validate.DefinitionVerifier

import System.Environment (getArgs, getProgName)
import Data.Text ( Text )
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

transformDefinitionFile :: String -> String -> IO ()
transformDefinitionFile inputFileName outputFileName = do
    contents <- Data.Text.IO.readFile inputFileName
    let esParsedDefinition = Kore.Parser.parseKoreDefinition inputFileName contents
    case esParsedDefinition of
        Left s
            -> do
                Prelude.putStrLn $ "cannot parse: " ++ s
        Right parsedDefinition
            -> do
                let transformed = transformDefinition parsedDefinition
                let unparsedDefinition = unparse transformed
                System.IO.withFile outputFileName WriteMode $ \outputFileHandle ->
                    Pretty.hPutDoc outputFileHandle unparsedDefinition


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


main :: IO ()
main = do
    args <- System.Environment.getArgs
    case args of
        "transform":args
            -> transform args
        "validate":args
            -> Prelude.putStrLn $ "NotImplemented"
        _ -> usage