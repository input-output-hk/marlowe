module TreeVisualise(GraphData, visualise, renderToFile) where

import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Graph
import Data.GraphViz.Attributes.Complete(Attribute(..),Label(StrLabel))
import Data.GraphViz
import Data.Text.Lazy (pack)

type GraphData = ([(Int, String)], [(Int, Int, String)])

getStates :: GraphData -> [(Int, DNode)]
getStates (a, _) = map (\(x, y) -> (x, DNode y)) a

getTransitions :: GraphData -> [(Int, Int, DTran)]
getTransitions (_, b) = map (\(x, y, z) -> (x, y, DTran z)) b

toGr :: GraphData -> Gr DNode DTran
toGr x = mkGraph (getStates x) (getTransitions x)

data DNode = DNode String
  deriving (Eq, Show, Ord)

instance Labellable DNode where
  toLabelValue (DNode s) = StrLabel (pack $ s)

data DTran = DTran String
  deriving (Eq, Show, Ord)

instance Labellable DTran where
  toLabelValue (DTran s) = StrLabel (pack $ s)


ncp :: GraphvizParams Int DNode DTran () DNode
ncp = nonClusteredParams { fmtNode = \(_, n) -> decorateNode n
                         , fmtEdge = \(_, _, e) -> decorateEdge e }

visualise :: GraphData -> IO ()
visualise gd = runGraphvizCanvas' (graphToDot ncp $ toGr gd) Xlib

renderToFile :: FilePath -> GraphData -> IO FilePath
renderToFile path gd = runGraphvizCommand Dot (graphToDot ncp $ toGr gd) DotOutput path

decorateEdge :: DTran -> Attributes
decorateEdge (DTran x) = [ Label $ StrLabel $ pack x ]

decorateNode :: DNode -> Attributes
decorateNode (DNode x) = [ Label $ StrLabel $ pack x ]


