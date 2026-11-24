import YM.Integration.NativeCoveredCofactorLocalUpdate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Single-link integration of the exact covered cofactor.
The link variable is sampled using the actual G.probHaar and is inserted
by Function.update, as in Next.Rank.Axial.pull_link. The matching-flag
indicator stays inside the local integral. No lower bound, normalization
change, or unconditional whole-cofactor invariance is asserted. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCoveredCofactorHaar
open Function Finset Lattice Wilson RG Marker MeasureTheory
open RG3.Forms NativeCoveredCofactorLocalUpdate
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {G : Gauge} {n : Side} {P : Rep G n}

/-- The exact complete-flag fiber through the original field. -/
def flagFiber (P : Rep G n) (U : Config G n) (e : Edge (Site n)) : Set G.El :=
  {u | flags P.p.threshold (Function.update U e u) = flags P.p.threshold U}

theorem update_continuous (U : Config G n) (e : Edge (Site n)) :
    Continuous (fun u : G.El => Function.update U e u) := by
  exact continuous_const.update e continuous_id

theorem flagFiber_measurable (U : Config G n) (e : Edge (Site n)) :
    MeasurableSet (flagFiber P U e) := by
  exact (flags_measurable_eq P.p.threshold (flags P.p.threshold U)).preimage
    (update_continuous U e).measurable

omit [Fintype V] in
theorem cofactor_eq_indicator (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s) (e : Edge (Site n))
    (he : e.1 ∈ (P.activities.forced i).support) (u : G.El) :
    NativeTasteCoveredCofactor.cofactor D (Function.update U e u) i s =
      (flagFiber P U e).indicator (fun _ => remainingProduct D U i s) u := by
  rw [cofactor_update_factorization D hD hK U i s hU e u he]
  by_cases hu : u ∈ flagFiber P U e
  · rw [Set.indicator_of_mem hu]
    exact if_pos hu
  · rw [Set.indicator_of_notMem hu]
    exact if_neg hu

omit [Fintype V] in
/-- The cofactor's link restriction is integrable without a cofactor-price
assumption: it is a fixed finite vector times a measurable indicator. -/
theorem cofactor_link_integrable (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s) (e : Edge (Site n))
    (he : e.1 ∈ (P.activities.forced i).support) :
    Integrable (fun u : G.El =>
      NativeTasteCoveredCofactor.cofactor D (Function.update U e u) i s) G.probHaar := by
  have h : Integrable
      ((flagFiber P U e).indicator (fun _ : G.El => remainingProduct D U i s))
      G.probHaar :=
    (integrable_const _).indicator (flagFiber_measurable U e)
  exact h.congr (ae_of_all _ fun u =>
    (cofactor_eq_indicator D hD hK U i s hU e he u).symm)

omit [Fintype V] in
/-- Arbitrary complex local weights stay with the indicator. This is the
unconditional scalar-times-fixed-vector integral identity, not an
unconditional multiplication rule in the polynomial ring. -/
theorem weighted_cofactor_integral (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s) (e : Edge (Site n))
    (he : e.1 ∈ (P.activities.forced i).support) (f : G.El → ℂ) :
    (∫ u, f u • NativeTasteCoveredCofactor.cofactor D (Function.update U e u) i s
      ∂G.probHaar) =
      (∫ u in flagFiber P U e, f u ∂G.probHaar) • remainingProduct D U i s := by
  calc
    _ = ∫ u, (flagFiber P U e).indicator f u • remainingProduct D U i s
        ∂G.probHaar := by
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        change f u • NativeTasteCoveredCofactor.cofactor D (Function.update U e u) i s =
          (flagFiber P U e).indicator f u • remainingProduct D U i s
        rw [cofactor_eq_indicator D hD hK U i s hU e he u]
        by_cases hu : u ∈ flagFiber P U e
        · simp only [Set.indicator_of_mem hu]
        · simp only [Set.indicator_of_notMem hu, smul_zero, zero_smul]
    _ = (∫ u, (flagFiber P U e).indicator f u ∂G.probHaar) •
        remainingProduct D U i s :=
      integral_smul_const _ _
    _ = _ := by rw [integral_indicator (flagFiber_measurable U e)]

omit [Fintype V] in
/-- The remaining scalar is exactly the actual Haar probability of matching
ALL original flags. No positive lower bound on this probability is claimed. -/
theorem cofactor_integral (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s) (e : Edge (Site n))
    (he : e.1 ∈ (P.activities.forced i).support) :
    (∫ u, NativeTasteCoveredCofactor.cofactor D (Function.update U e u) i s
      ∂G.probHaar) =
      G.probHaar.real (flagFiber P U e) • remainingProduct D U i s := by
  calc
    _ = ∫ u, (flagFiber P U e).indicator (fun _ => remainingProduct D U i s) u
        ∂G.probHaar :=
      integral_congr_ae (ae_of_all _ fun u =>
        cofactor_eq_indicator D hD hK U i s hU e he u)
    _ = _ := integral_indicator_const _ (flagFiber_measurable U e)

end YM.Integration.NativeCoveredCofactorHaar
end
