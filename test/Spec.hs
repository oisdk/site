module Main where

import Test.MarkdownDocTest
import System.Directory
import Data.List
import Test.QuickCheck

docTestDir :: String -> IO ()
docTestDir dir = do
  posts <- getDirectoryContents dir
  mddoctest [ dir ++ post
            | post <- posts
            , "lhs.markdown" `isSuffixOf` post ]

main :: IO ()
main = do
  docTestDir "posts/"
  docTestDir "drafts/"
