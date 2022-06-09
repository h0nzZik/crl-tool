{-# LANGUAGE TemplateHaskell #-}
import Kore.Parser
import System.Environment (getArgs)
import Data.Text ( Text )
import Data.Text.IO

main :: IO ()
main = do
    Prelude.putStrLn "Hello, World!" ;
    (fileName:_) <- getArgs
    contents <- Data.Text.IO.readFile fileName
    print (parseKoreDefinition fileName contents)

