import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

notation f " ≫ " g => Asymptotics.IsBigO Filter.atTop g f
