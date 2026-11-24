import YM.Integration.SelectedCofactorPhysicalMoment
import YM.Integration.SelectedCofactorChamberMarginal

/-! On every admitted original packet, a complete inventory cutoff is a field
event independent of the choice of scalar spectator labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorFlagSelector
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate SelectedCofactorPacketIntegral
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags SelectedCofactorPhysicalMoment SelectedCofactorChamberMarginal
open scoped Classical BigOperators Topology
open SelectedCofactorPhysicalMoment SelectedCofactorChamberMarginal
variable {G : Gauge}
variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F} {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

/-- The field flag selection can be taken outside the entire original signed
spectator sum. The other ancestor or reflection labels stay in the same group. -/
theorem rooted_mask (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (P : Finset (Site n₀) → Prop) (U : Config G n₀) :
    rooted S x X (fun a => Q a ∧ P (covered S a)) U =
      if P (flags S.output.carrier.rep.p.threshold U) then rooted S x X Q U else 0 := by
  let J₀ : Set (ℕ × Finset ℕ) := {a | (rootEdge S a.1).1 ∈ X ∧ Q a}
  let K₀ : Set (ℕ × Finset ℕ) := {a | (rootEdge S a.1).1 ∈ X ∧ (Q a ∧ P (covered S a))}
  let f (a : ℕ × Finset ℕ) := packet S x a U
  change (∑' a : K₀, f a.val) = if _ then ∑' a : J₀, f a.val else 0
  rw [tsum_subtype K₀ f,tsum_subtype J₀ f]
  by_cases hw : P (flags S.output.carrier.rep.p.threshold U)
  · rw [if_pos hw]
    apply tsum_congr
    intro a
    by_cases hn : f a = 0
    · simp only [Set.indicator,hn,ite_self]
    · have he := (packet_covers S x a U hn).2
      simp only [Set.indicator,K₀,J₀,Set.mem_setOf_eq,he,hw,and_true]
      split_ifs <;> rfl
  · rw [if_neg hw]
    have hz (a : ℕ × Finset ℕ) : K₀.indicator f a = 0 := by
      by_cases hn : f a = 0
      · simp only [Set.indicator,hn,ite_self]
      · have he := (packet_covers S x a U hn).2
        simp only [Set.indicator,K₀,Set.mem_setOf_eq,he,hw,and_false,if_false]
    exact (tsum_congr hz).trans tsum_zero

/-- The exact sparse root numerator is an exterior integral with the physical
sparse-field event and the same complete signed scalar spectators. -/
theorem sparse_marginal (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (k : ℕ) (L : Poly B →L[ℂ] ℂ)
    (A₀ : Set (Edge (Site n₀))) (u : Fields G A₀) :
    marginal A₀ (fun U => L (rooted S x X (fun a => Q a ∧ (covered S a).card < k) U)) u =
      marginal A₀ (fun U => if (flags S.output.carrier.rep.p.threshold U).card < k then
        L (rooted S x X Q U) else 0) u := by
  apply integral_congr_ae
  apply ae_of_all
  intro y
  let U := (cut G A₀).symm (u,y)
  have he := rooted_mask S x X Q (fun v => v.card < k) U
  change L (rooted S x X (fun a => Q a ∧ (covered S a).card < k) U) = _
  rw [he]
  by_cases h : (flags S.output.carrier.rep.p.threshold U).card < k <;> simp only [h,if_true,if_false,map_zero,U]

end YM.Integration.SelectedCofactorFlagSelector
end
