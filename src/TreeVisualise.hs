module TreeVisualise(GraphData, visualise, renderToFile) where

import qualified Data.Graph.Inductive.PatriciaTree as PT
import Data.Graph.Inductive.Graph(mkGraph)
import Data.GraphViz.Attributes.Complete(Attribute(..),Label(StrLabel))
import Data.GraphViz(Labellable(..),Attributes,DotGraph,GraphvizParams(..),
                     GraphvizCommand(..),runGraphvizCommand,GraphvizCanvas(..),
                     GraphvizOutput(..),nonClusteredParams,graphToDot,runGraphvizCanvas')
import Data.Text.Lazy (pack)

type GraphData = ([(Int, String)], [(Int, Int, String)])

getStates :: GraphData -> [(Int, DNode)]
getStates (a, _) = map (\(x, y) -> (x, DNode y)) a

getTransitions :: GraphData -> [(Int, Int, DTran)]
getTransitions (_, b) = map (\(x, y, z) -> (x, y, DTran z)) b

toGr :: GraphData -> PT.Gr DNode DTran
toGr x = mkGraph (getStates x) (getTransitions x)

data DNode = DNode String
  deriving (Eq, Show, Ord)

instance Labellable DNode where
  toLabelValue (DNode s) = StrLabel (pack s)

data DTran = DTran String
  deriving (Eq, Show, Ord)

instance Labellable DTran where
  toLabelValue (DTran s) = StrLabel (pack s)


ncp :: GraphvizParams Int DNode DTran () DNode
ncp = nonClusteredParams { fmtNode = \(_, n) -> decorateNode n
                         , fmtEdge = \(_, _, e) -> decorateEdge e }

toDot :: PT.Gr DNode DTran -> DotGraph Int 
toDot = graphToDot ncp

visualise :: GraphData -> IO ()
visualise gd = runGraphvizCanvas' (toDot (toGr gd)) Xlib

renderToFile :: FilePath -> GraphData -> IO FilePath
renderToFile path gd = runGraphvizCommand Dot (toDot (toGr gd)) DotOutput path

decorateEdge :: DTran -> Attributes
decorateEdge (DTran x) = [ Label $ StrLabel $ pack x ]

decorateNode :: DNode -> Attributes
decorateNode (DNode x) = [ Label $ StrLabel $ pack x ]


