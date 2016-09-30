module Hakyll.Web.Series
  ( seriesField
  , buildSeries
  ) where

import           Control.Monad
import           Data.Foldable
import           Data.List                       (elemIndex)
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map
import           Data.Maybe
import           Hakyll
import           Prelude                         hiding (head)
import           Text.Blaze.Html                 (toHtml, toValue, (!))
import           Text.Blaze.Html.Renderer.String (renderHtml)
import qualified Text.Blaze.Html5                as H
import qualified Text.Blaze.Html5.Attributes     as A

-- data Series = Series
--   { seriesMap :: Map String [Identifier]
--   , seriesMakeId :: String -> Identifier
--   , seriesDependency :: Dependency }

getSeries :: MonadMetadata m => Identifier -> m [String]
getSeries =
  fmap (maybe [] (pure . trim) . Map.lookup "series") . getMetadata

buildSeries :: MonadMetadata m => Pattern -> (String -> Identifier) -> m Tags
buildSeries = buildTagsWith getSeries

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

seriesField :: Tags -> Context a
seriesField tags = field "series" $ \item -> do
    let ident = itemIdentifier item
    series <- getSeries ident
    fromMaybe (pure "") (compileSeries series tags ident)
