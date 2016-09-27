module Main where

import Test.MarkdownDocTest
import System.Directory
import Data.List

main :: IO ()
main = do
  posts <- getDirectoryContents "posts/"
  mddoctest [ "posts/" ++ post
            | post <- posts
            , "lhs.markdown" `isSuffixOf` post ]
