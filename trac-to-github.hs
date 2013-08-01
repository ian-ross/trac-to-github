{-# LANGUAGE OverloadedStrings #-}
----------------------------------------------------------------------
-- |
-- Brute-force conversion of Trac tickets to GitHub issues.  If you
-- have a Trac and you want to convert all the tickets to GitHub
-- issues, and you don't have direct access to the Trac database, this
-- may be of use.  It scrapes ticket information from a Trac website,
-- pulling both the CSV and HTML versions of the ticket pages to get
-- the basic information and all comments, then creates GitHub tickets
-- and associated comments as appropriate.
--
-- Deficiencies include, but are not limited to: only partial handling
-- of Trac markup; processing of comments requires scraping of
-- information from Trac HTML pages, which is error-prone; doesn't
-- maintain any information about user names for creators and
-- commenters.
--
-- Good points: works without too much pain; includes a link back to
-- the original Trac ticket in each GitHub issue; includes links to
-- any Trac attachments in GitHub issues.
--
-- WARNING: use at your own risk.  I'd suggest creating a test GitHub
-- repository to run this against before you run it for real!
--
----------------------------------------------------------------------
module Main where

import Control.Monad (forM_, mapM_, zipWithM_)
import qualified Control.Monad as CM
import Data.List (splitAt, nub)
import Data.Monoid
import Data.CSV.Conduit
import Data.CSV.Conduit.Parser.Text
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Read as TR
import qualified Data.Text.IO as TIO
import qualified Data.Text.ICU.Regex as RE
import System.FilePath
import System.Directory
import System.IO
import Network.HTTP
import Github.Repos
import Github.Issues
import Github.Issues.Comments
import Text.XML.HXT.Core
import Text.HandsomeSoup

-- | You need to supply an appropriate GitHub user name and password
-- here.  This user needs to have write access to the repository you
-- want to import issues into.
ghAuth :: GithubAuth
ghAuth = GithubBasicAuth "user-name" "password"

-- | The repository you want to import issues into: the user (possibly
-- an organisation name) is the ownder of the repo (not necessarily
-- the same as the authorisation user name).
ghUser, ghRepo :: String
ghUser = "haskell"
ghRepo = "c2hs"

-- | Base URL of the Trac from which you want to scrape tickets.
tracbase :: String
tracbase = "http://hackage.haskell.org/trac/c2hs"


-- | Convert (some) Trac markup to GitHub Markdown.
fixMarkup :: Text -> Text
fixMarkup = codeInline . codeBlocks where
  codeBlocks = codeFix "{{{\n" "\n```\n" "}}}" "```\n"
  codeInline = codeFix "{{{" "`" "}}}" "`"
  codeFix beg newbeg end newend tin = go tin
    where go t = case T.breakOn beg t of
            (_, "") -> emphasis t
            (pre, suf) -> emphasis pre <> newbeg <> T.drop (T.length beg) suf'
              where suf' = case T.breakOn end suf of
                      (_, "") -> emphasis suf
                      (pre', suf'') ->
                        pre' <> newend <> T.drop (T.length end) (go suf'')
  emphasis = T.replace "''" "*" . T.replace "'''" "**"

-- | Information about a Trac ticket that can be ascertained from the
-- CSV version of the ticket page.
data TracTicket = TracTicket
                  { ttId :: Int
                  , ttSummary :: Text
                  , ttReporter :: Text
                  , ttOwner :: Text
                  , ttDescription :: Text
                  , ttType :: Text
                  , ttStatus :: Text
                  , ttPriority :: Text
                  , ttMilestone :: Text
                  , ttComponent :: Text
                  , ttVersion :: Text
                  , ttResolution :: Text
                  , ttKeywords :: [Text]
                  , ttCc :: [Text]
                  } deriving (Eq, Show)

-- | Convert data pulled from the CSV page into a TracTicket.
makeTicket :: Row Text -> TracTicket
makeTicket [] = error "Empty row to makeTicket!"
makeTicket [tid, summ, rep, own, desc, typ, stat, pri,
            ms, comp, ver, res, kws, cc] =
  case TR.decimal tid of
    Left err -> error $ "FAILED TO MAKE TICKET: " ++ err
    Right (ntid, _) -> TracTicket ntid summ rep own (fixMarkup desc)
                       typ stat pri ms comp ver res
                       (T.splitOn "," kws) (T.splitOn "," cc)

-- | Make a line giving a link back to the original Trac ticket, plus
-- some timestamp information if it's available.
origLine :: TracTicket -> [String] -> String
origLine tick dates =
  "Bug imported from [C2HS Trac]" ++
  "(http://hackage.haskell.org/trac/c2hs/ticket/" ++
  show (ttId tick) ++ ")\n" ++ datestr ++ "\n----\n\n"
  where datestr = case dates of
          [] -> ""
          [d] -> "\nTrac ticket created: " ++ d ++ "\n"
          (d1:d2:_) -> "\nTrac ticket created: " ++ d1 ++
                       "; last modified: " ++ d2 ++ "\n"

-- | Make a line with ticket priority information.
priorityLine :: TracTicket -> String
priorityLine tick = case ttPriority tick of
  "normal" -> ""
  _ -> "\nPriority: " ++ T.unpack (ttPriority tick) ++ "\n\n----\n\n"

-- | Do we need to edit the GitHub issue after we've created it?  This
-- is needed if the Trac ticket was closed or if it has a type that we
-- want to represent with a GitHub issue label.
neededit :: TracTicket -> Bool
neededit tick = ttStatus tick == "closed" ||
                ttType tick == "defect" || ttType tick == "enhancement"

-- | Build the issue editing value: we may want to change the issue
-- state or the labels.
tickEdit :: TracTicket -> EditIssue
tickEdit tick = (statused . typeed) editOfIssue
  where statused e = if ttStatus tick == "close"
                     then e { editIssueState = Just "closed" }
                     else e
        typeed e = case ttType tick of
          "defect" -> e { editIssueLabels = Just ["bug"] }
          "enhancement" -> e { editIssueLabels = Just ["enhancement"] }
          _ -> e

-- | Process one ticket, given the ticket number, the contents of the
-- CSV page and the contents of the HTML page.  Extracts what
-- information we can from the CSV data and scrapes some extra
-- information (in particular, comments) from the HTML page.  Creates
-- the GitHub issue and any associated comments.
processTick :: Int -> Text -> String -> IO ()
processTick n csv html = do
  case parseCSV defCSVSettings csv of
    Left err -> putStrLn $ "Ticket #" ++ show n ++ ": " ++ err
    Right rs -> do
      let origtick = makeTicket $ rs !! 1
      let doc = parseHtml html
      attachUrls <- runX $
        doc >>> css "dl.attachments dt a[title~=View]" ! "href"
      rawAttachUrls <- runX $
        doc >>> css "dl.attachments dt a[title~=Download]" ! "href"
      mainDates <- fmap (map $ takeWhile (/= ' ')) $ runX $
        doc >>> css "div#ticket a.timeline" ! "title"
      let tick = case zipWith attachLine attachUrls rawAttachUrls of
            [] -> origtick
            as -> origtick { ttDescription = ttDescription origtick <>
                           "\n\n----" <>
                           "\nOriginal Trac ticket had attachments:\n\n" <>
                           T.concat as }
      comments <- runX . xshow $
        doc >>> pres >>> ps >>> tts >>> css "div.comment" >>> getChildren
      commentDates <-
        fmap (map $ ("Original comment date: " ++) . (takeWhile (/= ' '))) $
        runX $ doc >>> css "div.change a.timeline" ! "title"
      nt <- newTick tick mainDates
      case nt of
        Left err -> putStrLn $ "ERROR: " ++ show err
        Right iss -> do
          zipWithM_ (addComment iss) comments commentDates
      return ()
  where addComment i c d = do
          putStrLn $ "Creating comment..."
          let c' = case d of
                [] -> c
                _ -> d ++ "\n\n----\n\n" ++ c
          createComment ghAuth ghUser ghRepo (issueNumber i) c'
        pres = processTopDown
               ((getChildren >>> changeText backticks) `when` hasName "pre")
        backticks = ("\n\n```\n" ++) . (++ "\n```\n\n")
        ps = processTopDown (getChildren `when` (hasName "p"))
        tts = processTopDown
              ((getChildren >>> changeText backticks1) `when` hasName "tt")
        backticks1 = ("`" ++) . (++ "`")
        attachLine u ru = " * [" <> base <> "](" <> T.pack u <>
                          ")  ([Download](" <> T.pack ru <> "))\n"
          where base = T.pack $ takeFileName u

-- | Generate a new GitHub issue from Trac ticket information plus
-- some timestamps if we have them.
newTick :: TracTicket -> [String] -> IO (Either Error Issue)
newTick tick dates = do
  let title = T.unpack $ ttSummary tick
      body = T.unpack $ ttDescription tick
      orig = origLine tick dates
      prio = priorityLine tick
      iss = (newIssue title) { newIssueBody = Just $ orig ++ prio ++ body }
  r <- createIssue ghAuth ghUser ghRepo iss
  case r of
    Left err -> return $ Left err
    Right riss -> do
      putStrLn $ "Issue #" ++ show (issueNumber riss) ++ " created"
      case neededit tick of
        False -> return $ Right riss
        True -> editIssue ghAuth ghUser ghRepo
                (issueNumber riss) (tickEdit tick)

-- | Pull the CSV and HTML pages for a given Trac ticket.
getTick :: String -> Int -> IO (Text, String)
getTick tracurl n = do
  html <- simpleHTTP (getRequest url) >>= getResponseBody
  csv <- simpleHTTP (getRequest csvurl) >>= getResponseBody
  return (T.pack csv, html)
  where url = tracurl ++ "/ticket/" ++ show n
        csvurl = url ++ "?format=csv"

-- | Dumb main: no command-line arguments -- just set the values at
-- the top of this to appropriate values.  Hopefully, you're not going
-- to be using this more than once...
main :: IO ()
main = do
  forM_ [1..] $ \n -> do
    putStrLn $ "Getting ticket #" ++ show n
    (csv, html) <- getTick tracbase n
    processTick n csv html
