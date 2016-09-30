--------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

import           Control.Monad
import           Data.Char           (toUpper)
import           Data.Monoid
import           Hakyll
import           Hakyll.Web.Series
import           Text.Pandoc         (Pandoc)
import           Text.Pandoc.Options

--------------------------------------------------------------------------------
main :: IO ()
main = hakyll $ do
    match "images/*" $ do
        route   idRoute
        compile copyFileCompiler

    match "css/*" $ do
        route   idRoute
        compile compressCssCompiler

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
            posts <- recentFirst =<< loadAll pattrn
            let ctx = constField "title" title
                   <> listField "posts" postCtx (pure posts)
                   <> defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/tag.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    tagsRules series $ \serie pattrn -> do
        let title = toUpper (head serie) : tail serie
        route idRoute
        compile $ do
            posts <- chronological =<< loadAll pattrn
            let ctx = constField "title" title
                   <> listField "posts" postCtx (pure posts)
                   <> defaultContext

            makeItem ""
                >>= loadAndApplyTemplate "templates/series.html" ctx
                >>= loadAndApplyTemplate "templates/default.html" ctx
                >>= relativizeUrls

    match "posts/*" $ do
        route $ setExtension "html"
        compile $ readPandocOptionalBiblio
              <&> writePandocWith (def { writerHTMLMathMethod = MathML Nothing, writerHighlight = True })
              >>= loadAndApplyTemplate "templates/post.html"    (postCtxWithTags tags series)
              >>= saveSnapshot "content"
              >>= loadAndApplyTemplate "templates/default.html" (postCtxWithTags tags series)
              >>= relativizeUrls

    match "index.html" $ do
        route idRoute
        compile $ do
            posts <- recentFirst =<< loadAll "posts/*"
            let indexCtx =
                    listField "posts" postCtx (pure posts) <>
                    constField "title" "Home"              <>
                    defaultContext

            getResourceBody
                >>= applyAsTemplate indexCtx
                >>= loadAndApplyTemplate "templates/default.html" indexCtx
                >>= relativizeUrls

    create ["rss.xml"] $ do
        route idRoute
        compile $ do
            let feedCtx = postCtx <> bodyField "description"
            posts <- fmap (take 10) . recentFirst =<<
                loadAllSnapshots "posts/*" "content"
            renderRss feedConfiguration feedCtx posts

    match "templates/*" $ compile templateBodyCompiler

(<&>) :: Functor f => f a -> (a -> b) -> f b
x <&> f = f <$> x

readPandocOptionalBiblio :: Compiler (Item Pandoc)
readPandocOptionalBiblio = do
  item <- getUnderlying
  getMetadataField item "bibliography" >>= \case
    Nothing -> readPandocWith defaultHakyllReaderOptions =<< getResourceBody
    Just bibFile -> join $
      readPandocBiblio defaultHakyllReaderOptions
                   <$> load (fromFilePath "assets/csl/chicago.csl")
                   <*> load (fromFilePath ("assets/bib/" ++ bibFile))
                   <*> getResourceBody


--------------------------------------------------------------------------------
postCtxWithTags :: Tags -> Tags -> Context String
postCtxWithTags tags series = seriesField desc series
                           <> tagsField "tags" tags
                           <> postCtx
  where
    desc curNum seriesLen serieName = concat
      [ "Part ", show curNum, " from a ", show seriesLen, "-part series on ", serieName]

postCtx :: Context String
postCtx =
    dateField "date" "%B %e, %Y" <>
    defaultContext

feedConfiguration :: FeedConfiguration
feedConfiguration = FeedConfiguration
  { feedTitle = "Donnacha Oisin Kidney's Blog"
  , feedDescription = "Mainly writing about programming"
  , feedAuthorName = "Donnacha Oisin Kidney"
  , feedAuthorEmail = "mail@doisinkidney.com"
  , feedRoot = "http://oisdk.netsoc.co"}

