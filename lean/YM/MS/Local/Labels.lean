import YM.MS.Local.Physical

set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.Physical
open Function Filter Set Finset Plane Koszul Real Momentum Tensor Submodule
open Color Landau Detect Local BV Woven
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {h: ℤ} {r: ℕ}
structure Deck (G : Gauge) where
   carries (h : ℤ) (r : ℕ): Submodule ℝ (Law G)
   sup h r: carries h r ⊔ Null G h r = Allowed G h r
   disjoint h r: Disjoint (carries h r) (Null G h r)
namespace Deck
variable (B: Deck G)
lemma setting (G:Gauge) : Nonempty (Deck G) := by
    choose q hq using (fun h r=> Submodule.exists_isCompl (Null G h r)); refine ⟨⟨fun h r=> q h r ⊓ Allowed G h r, ?_, ?_⟩⟩
    · intro h r; rw [sup_comm,← sup_inf_assoc_of_le _ (null_subset G),(hq h r).sup_eq_top,top_inf_eq]
    exact fun h r=> (hq h r).disjoint.symm.mono_left inf_le_left
lemma le (B:Deck G) : B.carries h r ≤ Allowed G h r:= by rw [← B.sup]; exact le_sup_left
instance (B: Deck G) h r: FiniteDimensional ℝ (B.carries h r):= Module.Finite.of_injective (Submodule.inclusion B.le) (Submodule.inclusion_injective _)
abbrev BIndex (B:Deck G) h r:= Fin (Module.finrank ℝ (B.carries h r))
def raw (B:Deck G) h r (i:B.BIndex h r): Law G:= ((Module.finBasis ℝ (B.carries h r)) i).val
end Deck
end YM.MS.Local.Physical
