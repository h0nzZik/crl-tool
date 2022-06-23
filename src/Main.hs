{-# LANGUAGE TemplateHaskell #-}
import Kore.Parser
import Kore.Unparser

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


main :: IO ()
main = do
    Prelude.putStrLn "Hello, World!" ;
    args <- System.Environment.getArgs
    case args of
        [inputFileName, outputFileName]
          -> do
              Prelude.putStrLn $ "input: " ++ inputFileName ++ ", output: " ++ outputFileName
              transformDefinitionFile inputFileName outputFileName
        _ -> do
            name <- System.Environment.getProgName
            Prelude.putStrLn $ "Usage: " ++ name ++ " inputFileName outputFileName"
{-
    (fileName:_) <- getArgs
    contents <- Data.Text.IO.readFile fileName
    parsedDefinition <- Kore.Parser.parseKoreDefinition fileName contents
    print (parsedDefinition)

-}