import YM.Integration.SelectedCofactorResidualGeometry
import YM.Integration.WilsonGlobalForcedMoment

/-! Actual Wilson near-event price and the signed large-support remainder
on its original measurable complement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorAnchoredRegister
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Cells
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch LocalComparison LocalComparison.Global
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic MergeProof MergeProof.Accent OPE.Therm OPE.Therm.House
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate SelectedCofactorPacketIntegral
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F} {δ : ℝ} {ord : ℕ}
local notation "P₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "P₁" => C.path.rep datum.cutoff datum.period (datum.level+1)
local notation "nc" => C.side datum.level datum.period
local notation "nf" => C.side (datum.level+1) datum.period
local notation "w₀" => fun i => F.outputRadii i/F.kernelCosts i
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)
local notation "r₀" => Real.exp (Fintype.card V*ordinaryRate K I δ)


open Push.AbsoluteSums.Animals Push.GridApprox.Attach

/-- The radius is measured in the torus metric of the original coarse fields. -/
def window {n : Side} (roots : V → Site n) (r : ℕ) : Finset (Site n) :=
  Finset.univ.biUnion fun v => neighbors r (roots v)

omit [DecidableEq V] in
theorem card {n : Side} (roots : V → Site n) (r : ℕ) :
    (window roots r).card ≤ Fintype.card V * ballCost r := by
  apply (Finset.card_biUnion_le).trans
  calc
    ∑ v : V, (neighbors r (roots v)).card ≤ ∑ _v : V, ballCost r :=
      Finset.sum_le_sum fun v _ => neighbors_card r (roots v)
    _ = _ := by simp

def hot {n : Side} (t : ℝ) (X : Finset (Site n)) : Set (Config G n) :=
  {U | ∃ z ∈ X, z ∈ flags t U}

theorem measurable {n : Side} (t : ℝ) (X : Finset (Site n)) :
    MeasurableSet (hot (G:=G) t X) := by
  have he : hot (G:=G) t X = ⋃ z ∈ X, {U : Config G n | z ∈ flags t U} := by
    ext U
    simp [hot]
  rw [he]
  exact Finset.measurableSet_biUnion _ (fun z _ => (flags_open (G:=G) z t).measurableSet)

/-- Off the register the complete signed original group only contains large
distinguished supports, including in the presence of arbitrary exterior flags. -/
theorem cold (S : Chosen K I M) (H : Bounds S δ ord) (x : IndependentTests J.tests)
    (X : Set (Site nc)) (Q : (ℕ × Finset ℕ) → Prop) (b k : ℕ) (U : Config G nc)
    (hc : U ∉ hot S.output.carrier.rep.p.threshold
      (window F.coarseRoots ((k+1)*leg b))) :
    rooted S x X Q U = rooted S x X (fun a =>
      Q a ∧ k < coverNumber b (S.output.carrier.rep.activities.forced a.1).support) U := by
  apply SelectedCofactorResidualGeometry.only_large S H x X Q U b k
  intro v y hy
  apply le_of_not_gt
  intro less
  exact hc ⟨y,Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,(neighbors_mem _ _ _).2 less.le⟩,hy⟩

/-- The original product-Haar moment splits over a single field event and
its complement, keeping all signs inside the two Bochner integrals. -/
theorem split (hC : C.Makes) (S : Chosen K I M) (H : Bounds S δ ord)
    (x : IndependentTests J.tests) (X : Set (Site nc)) (Q : (ℕ × Finset ℕ) → Prop) (b k : ℕ) :
    let E := hot (G:=G) S.output.carrier.rep.p.threshold (window F.coarseRoots ((k+1)*leg b))
    let μ := prior G nc
    (∫ U, rooted S x X Q U ∂μ) = (∫ U in E, rooted S x X Q U ∂μ) +
      ∫ U in Eᶜ, rooted S x X (fun a =>
        Q a ∧ k < coverNumber b (S.output.carrier.rep.activities.forced a.1).support) U ∂μ := by
  intro E μ
  have hE : MeasurableSet E := measurable _ _
  obtain ⟨c,hb⟩ := (rooted_envelope hC S H x X Q).cost
  have hi : Integrable (rooted S x X Q) (prior G nc) := Integrable.of_bound
    (rooted_envelope hC S H x X Q).meas.aestronglyMeasurable c (ae_of_all _ hb)
  refine (integral_add_compl hE hi).symm.trans ?_
  congr 1
  exact setIntegral_congr_fun hE.compl fun U hU => cold S H x X Q b k U hU

/-- Explicit period-independent four-dimensional thermal price for the
entire signed physical numerator on the genuine event in the splitting. -/
theorem charged (hG : G.Simple) (hC : C.Makes) (good : SelectedWilsonRootMoment.Hot C datum.level)
    (S : Chosen K I M) (hLate : ActualSelectedCofactorFunding.start C hG hC (Fintype.card V) ≤ datum.level)
    (ht : cool C.path.levels datum.level ≤ S.output.carrier.rep.p.threshold)
    (hFine : I.carrier.rep.eval = (P₁).eval) (H : Bounds S δ ord) (x : IndependentTests J.tests)
    (a : ℝ) (paid : ∀ W, Poly.price w₀ (ActualSelectedModelIntegral.defect S (testInclusion J.tests x) W) ≤ a+c₀)
    (ha : 0 ≤ a+c₀*r₀) (b k : ℕ) :
    let r := (k+1)*leg b
    let E := hot (G:=G) S.output.carrier.rep.p.threshold (window F.coarseRoots r)
    ‖∫ U in E, (Poly.price w₀ (((P₀).eval U)⁻¹ • rooted S x Set.univ (fun _ => True) U) : ℂ)
      ∂scene C.path datum.cutoff datum.period datum.level‖ ≤
      (((Fintype.card V * ballCost r * (Fintype.card PlaqAxes * 4) : ℕ) : ℝ) *
        vanishP C.path.levels datum.level) * (a+c₀*r₀) := by
  let r := (k+1)*leg b
  let X := window F.coarseRoots r
  let E := hot (G:=G) S.output.carrier.rep.p.threshold X
  have hE : MeasurableSet E := measurable _ _
  let t := E.indicator (fun _ => (1:ℂ))
  have h1 (U) : ‖t U‖ ≤ 1 := by
    by_cases hu : U ∈ E <;> simp [t,hu]
  have env : Envelope t := ⟨measurable_const.indicator hE,1,h1⟩
  have hit (U) (hu : t U ≠ 0) : ∃ z ∈ X, z ∈ flags (cool C.path.levels datum.level) U := by
    have he : U ∈ E := by
      by_contra h
      exact hu (Set.indicator_of_notMem h _)
    obtain ⟨z,hz,hf⟩ := he
    obtain ⟨p,hp,hh⟩ := (flags_spec _ _ _).mp hf
    exact ⟨z,hz,(flags_spec _ _ _).mpr ⟨p,hp,ht.trans_lt hh⟩⟩
  have hb := WilsonGlobalForcedMoment.selected hG hC good S hLate hFine H x a paid X t env h1 hit
  let f (U : Config G nc) : ℂ := Poly.price w₀ (((P₀).eval U)⁻¹ • rooted S x Set.univ (fun _ => True) U)
  have he : (fun U => t U * f U) = E.indicator f := by
    funext U
    by_cases h : U ∈ E <;> simp [t,h]
  change ‖∫ U, t U * f U ∂_‖ ≤ _ at hb
  rw [he, integral_indicator hE] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ ha
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact_mod_cast Nat.mul_le_mul_right (Fintype.card PlaqAxes*4) (card F.coarseRoots r)

end YM.Integration.SelectedCofactorAnchoredRegister
