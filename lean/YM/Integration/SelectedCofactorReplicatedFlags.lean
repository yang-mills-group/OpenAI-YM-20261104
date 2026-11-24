import YM.Integration.SelectedCofactorConditionalSeries
import YM.Cells.Margins
import YM.Work.H03

/-! Flag incidence for original signed packet groups, including arbitrary
different groups and tests on the reflected physical cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorReplicatedFlags

open Function Finset Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorPacketIntegral SelectedCofactorConditionalSeries
open scoped Classical BigOperators Topology

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : Census V} {C : Family G} {J : Request V} {A : NumericSchedule C J}
    {datum : LocalFormal.Datum C B} {caps : Handoff.OutputCapacities}
    {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {forcedOrder : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "μ₀" => prior G n₀

/-- A signed packet retains its full distinguished inventory as actual
flagged sites, for every field at which the polynomial is nonzero. -/
theorem packet_inventory (S : Chosen K I M) (x : IndependentTests J.tests)
    (p : ℕ × Finset ℕ) (U : Config G n₀) (hn : packet S x p U ≠ 0) :
    (S.output.carrier.rep.activities.forced p.1).inventory ⊆ flags S.output.carrier.rep.p.threshold U := by
  have h : admitted S.output.carrier.rep U p.1 p.2 := by
    by_contra ha
    exact hn (by rw [packet, cofactor_eq_if, if_neg ha, mul_zero])
  exact h.2.2.1

/-- Signed packets whose distinguished sites lie in X. The selector Q
retains any specified additional address or ancestor labels. -/
def rooted (S : Chosen K I M) (x : IndependentTests J.tests) (X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (U : Config G n₀) : Poly B :=
  ∑' p : {p : ℕ × Finset ℕ // (rootEdge S p.1).1 ∈ X ∧ Q p}, packet S x p.val U

theorem rooted_envelope (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) :
    Envelope (rooted S x X Q) := by
  obtain ⟨D, hD, hb⟩ := packet_dominated hC S H x
  let T := {p : ℕ × Finset ℕ // (rootEdge S p.1).1 ∈ X ∧ Q p}
  have h : Dominated (fun (p : T) => packet S x p.val) :=
    ⟨fun p => D p.val, hD.subtype _, fun p => hb p.val⟩
  exact ⟨Measurable.tsum fun p => packet_measurable hC S H x p.val, h.bound⟩

theorem rooted_integral (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta forcedOrder)
    (x : IndependentTests J.tests) (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) :
    (∫ U, rooted S x X Q U ∂μ₀) =
      ∑' p : {p : ℕ × Finset ℕ // (rootEdge S p.1).1 ∈ X ∧ Q p}, exteriorPacket S x p.val := by
  obtain ⟨hI, hA⟩ := packet_absolute hC S H x
  let T := {p : ℕ × Finset ℕ // (rootEdge S p.1).1 ∈ X ∧ Q p}
  have hs : Summable (fun p : T => ∫ U, ‖packet S x p.val U‖ ∂μ₀) := hA.subtype _
  have hi : ∀ p : T, Integrable (packet S x p.val) μ₀ := fun p => hI p.val
  exact (integral_tsum_of_summable_integral_norm (F := fun p : T => packet S x p.val) hi hs).symm.trans
    (tsum_congr fun p => packet_integral hC S H x p.val)

/-- Any nonzero detected signed group has a genuine distinguished flag
in its root set, also for every smaller physical flag threshold. -/
theorem rooted_flag (S : Chosen K I M) (x : IndependentTests J.tests)
    (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop) (L : Poly B →L[ℂ] ℂ)
    {t : ℝ} (ht : t ≤ S.output.carrier.rep.p.threshold) (U : Config G n₀)
    (hn : L (rooted S x X Q U) ≠ 0) : ∃ z ∈ X, z ∈ flags t U := by
  by_contra h
  apply hn
  have hz (p : {p : ℕ × Finset ℕ // (rootEdge S p.1).1 ∈ X ∧ Q p}) :
      packet S x p.val U = 0 := by
    by_contra hp
    have hm := packet_inventory S x p.val U hp
      (S.output.carrier.rep.activities.forced p.val.1).inventory_ne.choose_spec
    obtain ⟨f,hf,hb⟩ := (flags_spec _ _ _).1 hm
    exact h ⟨(rootEdge S p.val.1).1, p.property.1, (flags_spec _ _ _).2 ⟨f,hf,ht.trans_lt hb⟩⟩
  rw [rooted, tsum_congr hz, tsum_zero, map_zero]

/-- Every nonzero product of the actual reflected groups needs one
distinct physical flagged site in each chamber. All other links, modes
and packet partners stay in their signed factors. -/
theorem replicated_flags (S : Chosen K I M) (T : Tiling n₀) (x : T.Cell → IndependentTests J.tests)
    (X : T.Cell → Set (Site n₀)) (hX : ∀ i, X i ⊆ T.chamber 0)
    (Q : T.Cell → (ℕ × Finset ℕ) → Prop) (L : T.Cell → Poly B →L[ℂ] ℂ)
    {t : ℝ} (ht : t ≤ S.output.carrier.rep.p.threshold) (U : Config G n₀)
    (hn : T.fullAt (fun i W => L i (rooted S (x i) (X i) (Q i) W)) U ≠ 0) :
    Fintype.card T.Cell ≤ (flags t U).card := by
  have hcell (i : T.Cell) :
      L i (rooted S (x i) (X i) (Q i) (pull (T.omega i) (T.translateBy i) U)) ≠ 0 := by
    intro h
    apply hn
    unfold Tiling.fullAt
    apply prod_eq_zero (mem_univ i)
    unfold Tiling.copy
    split <;> simp only [h, star_zero]
  have hsite (i : T.Cell) : ∃ z ∈ T.chamber i, z ∈ flags t U := by
    obtain ⟨z,hz,hd⟩ := rooted_flag S (x i) (X i) (Q i) (L i) ht _ (hcell i)
    refine ⟨T.copyMap i z, T.enumerate i (hX i hz), ?_⟩
    rw [← Work.H03.flags_send (T.omega i) (T.translateBy i) t U]
    exact mem_image.mpr ⟨z,hd,rfl⟩
  choose z hz hd using hsite
  have hi : Function.Injective z := fun i j h =>
    (T.which_chamber (hz i)).symm.trans ((congrArg T.which h).trans (T.which_chamber (hz j)))
  exact (card_univ (α := T.Cell)).symm.trans_le
    (Finset.card_le_card_of_injOn (f := z) (fun i _ => hd i) hi.injOn)

end YM.Integration.SelectedCofactorReplicatedFlags
end
