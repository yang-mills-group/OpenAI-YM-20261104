import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace YM.MS.Shine
open Filter
open scoped Topology
abbrev dotty := 𝓝[≠] (0:ℂ)
lemma dotty_non : ∀ᶠ i in dotty, i≠0:= self_mem_nhdsWithin
end YM.MS.Shine
