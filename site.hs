--------------------------------------------------------------------------------
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

import           Control.Monad
import           Data.Foldable
import qualified Data.Map.Strict                 as Map
import           Data.Monoid
import           Hakyll
import           Prelude                         hiding (head)
import           Text.Blaze.Html                 (toHtml, toValue, (!))
import           Text.Blaze.Html.Renderer.String (renderHtml)
import qualified Text.Blaze.Html5                as H
import qualified Text.Blaze.Html5.Attributes     as A
import           Text.Pandoc                     (Pandoc)
import           Text.Pandoc.Options
import Data.Maybe
import Data.List (elemIndex)

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

    -- build up tags
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
        let title = "Series on " ++ serie
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
postCtxWithTags tags series = seriesField series <> tagsField "tags" tags <> postCtx

seriesField :: Tags
              -- ^ Tags structure
              -> Context a
              -- ^ Resulting context
seriesField tags = field "series" $ \item -> do
    let ident = itemIdentifier item
    series <- getSeries ident
    fromMaybe (pure "") (compileSeries series tags ident)

head :: Foldable f => f a -> Maybe a
head = foldr (\e _ -> Just e) Nothing

compileSeries :: [String] -> Tags -> Identifier -> Maybe (Compiler String)
compileSeries series tags ident = do
  serie <- head series
  otherPostsInSeries <- lookup serie (tagsMap tags)
  let seriesLen = length otherPostsInSeries
  curInd <- elemIndex ident otherPostsInSeries
  let curNum = curInd + 1
  let desc = concat ["Part ", show curNum, " from a ", show seriesLen, "-part series on ", serie]
  let renderLink link = renderHtml $ H.a ! A.href (toValue $ toUrl link) $ toHtml desc
  pure $ foldMap renderLink <$> getRoute (tagsMakeId tags serie)

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

getSeries :: MonadMetadata m => Identifier -> m [String]
getSeries =
  fmap (maybe [] (pure . trim) . Map.lookup "series") . getMetadata

buildSeries :: MonadMetadata m => Pattern -> (String -> Identifier) -> m Tags
buildSeries = buildTagsWith getSeries

