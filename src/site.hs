--------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

import           Control.Monad

import           Data.Char           (toUpper)

import qualified Data.Map            as Map

import           Data.Maybe
import           Data.Monoid

import           Hakyll
import           Hakyll.Web.Series

import qualified Text.CSL            as CSL
import           Text.CSL.Pandoc     (processCites)
import           Text.Pandoc
import           Text.Pandoc.Highlighting

--------------------------------------------------------------------------------
main :: IO ()
main = hakyllWith (defaultConfiguration {deployCommand=command}) $ do

    match "CNAME" $ do
      route   idRoute
      compile copyFileCompiler

    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "pdfs/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "code/*/*" $ do
        route idRoute
        compile $ getResourceString
              >>= relativizeUrls

    match "css/default.css" $ compile cssTemplateCompiler

    match (fromList ["about.markdown", "contact.markdown"]) $ do
        route   $ setExtension "html"
        compile $ pandocCompiler
            >>= loadAndApplyTemplate "templates/default.html" defaultContext
            >>= relativizeUrls

    match "assets/csl/*" $ compile cslCompiler

    match "assets/bib/*" $ compile biblioCompiler

    tags <- buildTags "posts/*" (fromCapture "tags/*.html")

    series <- buildSeries "posts/*" (fromCapture "series/*.html")

    tagsRules tags $ \tag pattrn -> do
        let title = "Posts tagged \"" ++ tag ++ "\""
        route idRoute
        compile $ do
            let ctx = postListCtx title $ recentFirst =<< loadAll pattrn
            makeItem ""
                >>= loadAndApplyTemplate "templates/tag.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    tagsRules series $ \(s:erie) pattrn -> do
        let title = toUpper s : erie
        route idRoute
        compile $ do
            let ctx = postListCtx title $ chronological =<< loadAll pattrn
            makeItem ""
                >>= loadAndApplyTemplate "templates/series.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    match "posts/*" $ do
        let ctx = postFullCtx tags series
        route $ setExtension "html"
        compile $ postCompiler
              >>= loadAndApplyTemplate "templates/post.html"    ctx
              >>= saveSnapshot "content"
              >>= loadAndApplyTemplate "templates/default.html" ctx
              >>= relativizeUrls


    match "snippets/*" $ do
        let ctx = defaultContext
        route $ setExtension "html"
        compile $ postCompiler
              >>= loadAndApplyTemplate "templates/snippet.html" ctx
              >>= saveSnapshot "content"
              >>= loadAndApplyTemplate "templates/default.html" ctx
              >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            let indexCtx = postListCtx "Posts" $ recentFirst =<< loadAll "posts/*"
            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    version "redirects" $ createRedirects oldLinks

    -- match "snippets.html" $ do
    --     route idRoute
    --     compile $ do
    --         let indexCtx = snippetListCtx "Code Snippets" $ loadAll "snippets/*"
    --         getResourceBody
    --             >>= applyAsTemplate indexCtx
    --             >>= loadAndApplyTemplate "templates/default.html" indexCtx
    --             >>= relativizeUrls

    create ["rss.xml"] $ do
        route idRoute
        compile $ do
            let feedCtx = postCtx <> bodyField "description"
            posts <- recentFirst =<<
                loadAllSnapshots "posts/*" "content"
            renderRss feedConfiguration feedCtx posts

    match "templates/*" $ compile templateBodyCompiler


--------------------------------------------------------------------------------

postCompiler :: Compiler (Item String)
postCompiler =
  writePandocWith (def { writerHTMLMathMethod = MathML
                       , writerHighlightStyle = Just kate }) <$>
  readPandocOptionalBiblio

cssTemplateCompiler :: Compiler (Item Hakyll.Template)
cssTemplateCompiler = cached "Hakyll.Web.Template.cssTemplateCompiler" $
    fmap (readTemplate . compressCss) <$> getResourceString

readPandocBiblioLinkCit :: ReaderOptions
                   -> Item CSL
                   -> Item Biblio
                   -> Item String
                   -> Compiler (Item Pandoc)
readPandocBiblioLinkCit ropt csl biblio item = do
    -- Parse CSL file, if given
    style <- unsafeCompiler $ CSL.readCSLFile Nothing . toFilePath . itemIdentifier $ csl

    -- We need to know the citation keys, add them *before* actually parsing the
    -- actual page. If we don't do this, pandoc won't even consider them
    -- citations!
    let Biblio refs = itemBody biblio
    pandoc <- itemBody <$> readPandocWith ropt item
    let pandoc' = processCites style refs (addLinkCitations pandoc) -- here's the change

    return $ fmap (const pandoc') item

addLinkCitations :: Pandoc -> Pandoc
addLinkCitations (Pandoc meta a) =
  let prevMap = unMeta meta
      newMap = Map.insert "link-citations" (MetaBool True) prevMap
      newMeta = Meta newMap
  in  Pandoc newMeta a

pandocOptions :: Compiler ReaderOptions
pandocOptions = do
  item <- getUnderlying
  getMetadataField item "literate-haskell" >>= \case
    Nothing -> pure defaultHakyllReaderOptions
    Just _ -> pure (defaultHakyllReaderOptions {readerExtensions = enableExtension Ext_literate_haskell (readerExtensions defaultHakyllReaderOptions)})

readPandocOptionalBiblio :: Compiler (Item Pandoc)
readPandocOptionalBiblio = do
  item <- getUnderlying
  options <- pandocOptions
  getMetadataField item "bibliography" >>= \case
    Nothing -> readPandocWith options =<< getResourceBody
    Just bibFile -> do
      maybeCsl <- getMetadataField item "csl"
      join $ readPandocBiblioLinkCit options
                          <$> load (fromFilePath ("assets/csl/" ++ fromMaybe "chicago.csl" maybeCsl))
                          <*> load (fromFilePath ("assets/bib/" ++ bibFile))
                          <*> getResourceBody

--------------------------------------------------------------------------------

postCtx :: Context String
postCtx = mconcat
    [ dateField "date" "%B %e, %Y"
    , defaultContext ]

postFullCtx :: Tags -> Tags -> Context String
postFullCtx tags series = mconcat
  [ seriesField series
  , tagsField "tags" tags
  , postCtx ]


postListCtx :: String -> Compiler [Item String] -> Context String
postListCtx title posts = mconcat
  [ listField "posts" postCtx posts
  , constField "title" title
  , defaultContext ]

-- snippetListCtx :: String -> Compiler [Item String] -> Context String
-- snippetListCtx title snippets = mconcat
--   [ listField "snippets" defaultContext snippets
--   , constField "title" title
--   , defaultContext ]

--------------------------------------------------------------------------------

oldLinks :: [(Identifier, String)]
oldLinks =
  [ ("snippets/2048.html"           , "/posts/2015-10-20-2048.html")
  , ("snippets/ListSyntax.html"     , "/posts/2019-04-20-ListSyntax.html")
  , ("snippets/convolutions.html"   , "/posts/2018-03-19-convolutions-lhs.html")
  , ("snippets/drawing-trees.html"  , "/posts/2018-12-30-drawing-trees-lhs.html")
  , ("snippets/nary-uncurry.html"   , "/posts/2018-12-29-nary-uncurry-lhs.html")
  , ("snippets/one-pass-choose.html", "/posts/2018-03-15-one-pass-choose-lhs.html")
  , ("snippets/rotations.html"      , "/posts/2018-06-03-rotations-lhs.html")
  , ("snippets/strictify.html"      , "/posts/2018-03-21-strictify-lhs.html")
  , ("snippets/swapping.html"       , "/posts/2018-05-30-swapping-lhs.html")
  , ("snippets/unfoldl.html"        , "/posts/2017-12-14-unfoldl-lhs.html")
  , ("snippets/unparsing.html"      , "/posts/2017-04-01-unparsing-lhs.html")
  , ("snippets.html"                , "/index.html")
  ]

--------------------------------------------------------------------------------

feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
  { feedTitle = "Donnacha Oisín Kidney's Blog"
  , feedDescription = "Mainly writing about programming"
  , feedAuthorName = "Donnacha Oisín Kidney"
  , feedAuthorEmail = "mail@doisinkidney.com"
  , feedRoot = "https://doisinkidney.com"}


command :: String
command = unlines
 [ "git stash"
 , "git checkout develop"
 , "stack exec site clean"
 , "stack exec site build"
 , "git fetch --all"
 , "git checkout -b master --track origin/master"
 , "rsync -a --filter='P _site/'      "
 ++ "        --filter='P _cache/'     "
 ++ "        --filter='P .git/'       "
 ++ "        --filter='P .gitignore'  "
 ++ "        --filter='P .stack-work' "
 ++ "        --delete-excluded        "
 ++ "        _site/ ."
 , "git add -A"
 , "git commit -m \"Publish.\""
 , "git push origin master:master"
 , "git checkout develop"
 , "git branch -D master"
 , "git stash pop"]
