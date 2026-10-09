import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import SYKBlueprint.Model
import SYKBlueprint.GaussianConcentration
import SYKBlueprint.SuperConcentration
import SYKBlueprint.CLT

set_option linter.mathlibStandardSet false

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Formalization Blueprint for the SYK Model" =>

This Blueprint records the finite-dimensional SYK model, Gaussian concentration,
superconcentration, and the conditional central limit theorem, with
their mathematical dependencies.
It distinguishes declarations already checked by Lean from results that remain to be
formalized.

{include 0 SYKBlueprint.Model}
{include 0 SYKBlueprint.GaussianConcentration}
{include 0 SYKBlueprint.SuperConcentration}
{include 0 SYKBlueprint.CLT}

{blueprint_graph}
{blueprint_summary}
