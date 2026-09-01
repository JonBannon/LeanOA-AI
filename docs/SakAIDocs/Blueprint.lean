import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SakAIDocs.Chapters.Overview
import SakAIDocs.Chapters.CStarAndTopologies
import SakAIDocs.Chapters.Order
import SakAIDocs.Chapters.Projections
import SakAIDocs.Chapters.PositiveFunctionals
import SakAIDocs.Chapters.Stonean
import SakAIDocs.Chapters.Normality
import SakAIDocs.Chapters.KaplanskyDensity
import SakAIDocs.Chapters.SupportProjections
import SakAIDocs.Chapters.SpectralResolution
import SakAIDocs.Chapters.PolarDecomposition
import SakAIDocs.Chapters.FunctionalSupport
import SakAIDocs.Chapters.Library

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sak-AI" =>

%%%
authors := ["Jon Bannon and AI collaborators"]
shortTitle := "Sak-AI"
%%%

Sak-AI is a machine-checked operator-algebra library organized around a
long-term formalization of Sakai's _C-star Algebras and W-star Algebras_.  The book
guides the mathematical reading order; Mathlib-quality reusable interfaces
guide the Lean API.

{include 0 SakAIDocs.Chapters.Overview}

{include 0 SakAIDocs.Chapters.CStarAndTopologies}

{include 0 SakAIDocs.Chapters.Order}

{include 0 SakAIDocs.Chapters.Projections}

{include 0 SakAIDocs.Chapters.PositiveFunctionals}

{include 0 SakAIDocs.Chapters.Stonean}

{include 0 SakAIDocs.Chapters.Normality}

{include 0 SakAIDocs.Chapters.KaplanskyDensity}

{include 0 SakAIDocs.Chapters.SupportProjections}

{include 0 SakAIDocs.Chapters.SpectralResolution}

{include 0 SakAIDocs.Chapters.PolarDecomposition}

{include 0 SakAIDocs.Chapters.FunctionalSupport}

{include 0 SakAIDocs.Chapters.Library}

{blueprint_graph (direction := LR)}

{blueprint_summary}

# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
