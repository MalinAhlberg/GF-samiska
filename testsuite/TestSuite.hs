module TestSuite (main) where

import Data.Char
import Data.List
import Data.Maybe
import System.FilePath.Posix
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.Directory
import Control.Monad
import System.IO
import PGF

type Sentence = (Int,String)

main :: IO ()
main = do args <- getArgs
          let (b,maybeFile) = checkArgs args
          case maybeFile of
             Just filePath -> do
                runFile b filePath
                exitSuccess
             Nothing      -> do 
                putStrLn "Usage: runghc TestSuite [-v] [filePath]"
            	exitFailure
                
runFile :: Bool -> FilePath -> IO ()
runFile b filePath = do
        fileContent <- readFile filePath 
        pgf <- readPGF "Lang.pgf"                
        let allLines = lines fileContent
        let sentences = pair . filter ((/= '-') . head . snd) $ filter (not . null . snd) (zip [2..] allLines)
        putStrLn $ "Testing sentence in: " ++ takeFileName filePath
        bs <- mapM (compTransl pgf b) sentences
        putStrLn $ show (length (filter (==True) bs)) ++ " of " ++ show (length bs) ++ " sentences passed"

pair :: [(Int,String)] -> [(Sentence,Sentence)]
pair []         = []
pair [(_,"\n")] = [] 
pair [x]        = error "couldn't match english and saami sentences"
pair (eng:sam:xs) = (eng,sam):pair xs

checkArgs :: [String] -> (Bool, Maybe FilePath)
checkArgs = (flip checkArgs') (False, Nothing)

checkArgs' :: [String] -> (Bool, Maybe FilePath) -> (Bool, Maybe FilePath)
checkArgs' [] r            = r
checkArgs' ("-v":xs) (_,f) = checkArgs' xs (True,f)
checkArgs' (x:xs) (b,_)    = (b, Just x) 

compTransl :: PGF -> Bool -> (Sentence,Sentence) -> IO Bool
compTransl pgf verbose ((line,eng),(_,expected)) = do
   let maybeReceived = translateS pgf eng
   case maybeReceived of
      Nothing       -> showLine >> putStrLn eng >> 
                       putStrLn "Unable to parse sentence\n" >> return False
      Just received -> do
        let asExpected = any (expected ==) received
        when (not asExpected) (mapM_ putStrLn received)
        let c = if asExpected then green else red
        when (verbose || not asExpected) $ showLine >> putStrLn eng
                >> putStrLn ( "The expected answer was: " ++ color c expected )
                >> putStrLn ( "The received answer was: " 
                               ++ color c (intercalate ". " received) ++ "\n" )  
        return asExpected
  where showLine    = putStrLn $ "Sentence on line " ++ show line



translateS :: PGF -> String -> Maybe [String]
translateS pgf s = case parsed of
                     [] -> Nothing
                     ts -> Just $ concatMap (linearizeS pgf) ts
   where parsed = parse pgf (fromJust $ readLanguage "LangEng") (fromJust $ readType "Utt") s

linearizeS :: PGF -> Tree -> [String]
linearizeS pgf tree = sentens
   where 
        samLang = (fromJust $ readLanguage "LangSam")
   	allLang = tabularLinearizes pgf samLang tree
   	samS    = concat allLang
   	sentens = map snd samS


test = "Mary is green \n Merjá lea unni"

-- Terminal color output, stolen from Compiler Construction testsuite 

type Color = Int

color :: Color -> String -> String
color c s = fgcol c ++ s ++ normal

normal = "\ESC[0m"

bold :: String -> String
bold = ("\ESC[1m" ++)


fgcol :: Int -> String
fgcol col = "\ESC[0" ++ show (30+col) ++ "m"


red, green, blue,pink :: Color
red = 1
green = 2
blue = 4
pink = 5
