module Main where

import Test.MarkdownDocTest

main :: IO ()
main = mddoctest ["posts/2016-09-27-odds.markdown"]
