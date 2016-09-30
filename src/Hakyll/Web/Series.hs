module Hakyll.Web.Series
  ( seriesField
  , buildSeries
  ) where

import           Control.Monad
import           Data.Foldable
import           Data.List                       (elemIndex)
import qualified Data.Map.Strict                 as Map
import           Data.Maybe
import           Hakyll
import           Prelude                         hiding (head)
import           Text.Blaze.Html                 (toHtml, toValue, (!))
import           Text.Blaze.Html.Renderer.String (renderHtml)
import qualified Text.Blaze.Html5                as H
import qualified Text.Blaze.Html5.Attributes     as A
import qualified Data.Set as Set

getSeries :: MonadMetadata m => Identifier -> m (Maybe String)
getSeries =
  fmap (fmap trim . Map.lookup "series") . getMetadata

compileSeries :: String -> Tags -> Identifier -> Maybe (Compiler String)
compileSeries serie tags ident = do
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
    fromMaybe (pure "") (series >>= \serie -> compileSeries serie tags ident)

buildSeries :: MonadMetadata m
            => Pattern
            -> (String -> Identifier)
            -> m Tags
buildSeries pattrn makeId = do
    ids    <- getMatches pattrn
    tagMap <- foldM addTags Map.empty ids
    let set' = Set.fromList ids
    return $ Tags (Map.assocs tagMap) makeId (PatternDependency pattrn set')
  where
    -- Create a tag map for one page
    addTags tagMap id' =
        maybe tagMap (\k -> Map.insertWith (flip (++)) k [id'] tagMap) <$> getSeries id'
