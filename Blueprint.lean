import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SYK.Chapters.Model
import SYK.Chapters.GaussianConcentration
import SYK.Chapters.SuperConcentration
import SYK.Chapters.CLT

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Formalization Blueprint for the SYK Model" =>

This Blueprint records the mathematical dependencies shared by the finite-dimensional
SYK model, Gaussian concentration, superconcentration, and the central limit theorem.
It distinguishes declarations already checked by Lean from results that remain to be
formalized.

{include 0 SYK.Chapters.Model}
{include 0 SYK.Chapters.GaussianConcentration}
{include 0 SYK.Chapters.SuperConcentration}
{include 0 SYK.Chapters.CLT}

{blueprint_graph}
{blueprint_summary}
