import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTestedCorrelationExpansion
import YM.Integration.WilsonMSbarStandaloneCorrelation

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YangMills.Matching.CorrelationOnly
open Filter Set MeasureTheory
open scoped Topology BigOperators Classical ContDiff

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

theorem clockAtZero (H : Measurement B T) : Tendsto H.clock (𝓝[>] 0) (𝓝 0) := by
  let a : ℝ := 2 * oneLoopBeta B
  let root := fun r : ℝ => Real.sqrt (a * Real.log r⁻¹)
  have logs : Tendsto (fun r : ℝ => Real.log r⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have normalized : Tendsto (fun r => H.clock r * root r) (𝓝[>] 0) (𝓝 1) := H.oneLoop
  have hnorm := normalized.eventually_const_lt (by norm_num : (0:ℝ) < 1)
  have hlog := logs.eventually (eventually_gt_atTop (0:ℝ))
  obtain ⟨s, hc, hprod, hl⟩ := (H.positive.and (hnorm.and hlog)).exists
  have hroot : 0 < root s := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact False.elim (lt_asymm hc h.1)
  have ha : 0 < a := (mul_pos_iff_of_pos_right hl).mp (Real.sqrt_pos.mp hroot)
  have big : Tendsto root (𝓝[>] 0) atTop :=
    Real.tendsto_sqrt_atTop.comp (Filter.Tendsto.const_mul_atTop ha logs)
  have inv : Tendsto (fun r => (root r)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp big
  have identify : (fun r => (H.clock r * root r) * (root r)⁻¹) =ᶠ[𝓝[>] 0] H.clock := by
    filter_upwards [big.eventually (eventually_gt_atTop (0:ℝ))] with r hr
    simp [hr.ne']
  simpa using (normalized.mul inv).congr' identify

def ShapeIncome (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T) : Prop :=
  ∀ (n p j : ℕ) (d : Fin n → ℕ) (K : Set (Points n))
      (_compact : IsCompact K) (_separated : K ⊆ WilsonFamily.separated n),
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (phase : Option T.Character)
      (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) (x : Points n), x ∈ K →
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      shapeJetEstimateAt j
        (fun y => T.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • y i))
        (fun y => ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * S.correlation M k.val a y)
        x (A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1))

theorem measuredEstimates (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T)
    (shapes : ShapeIncome M S H) (phases : PhaseProximity H)
    (independent : ∃! P : WardStress.Series B, WardStress.Determined M S P)
    (named : ∀ P : WardStress.Series B, WardStress.Determined M S P → namedStress H P) :
    Estimates M S H where
  tested n d := by
    refine ⟨0, ?_⟩
    intro phase v o
    apply testedOfShapeJets H.positive (clockAtZero H)
    intro p K hK clear
    obtain ⟨A, hA, late⟩ := shapes n p 0 d K hK clear
    refine ⟨A * (∏ i, sectorMass (v i)),
      mul_nonneg hA (Finset.prod_nonneg fun i _ => sectorMass_nonneg (v i)), ?_⟩
    exact late.mono fun s hs x hx => hs phase v o x hx
  compact n p d o K hK clear := by
    obtain ⟨A, hA, late⟩ := shapes n p 0 d K hK clear
    exact ⟨A, hA, late.mono fun s hs phase v x hx => shapeValue (hs phase v o x hx)⟩
  jets := shapes
  phases := phases
  wardIndependent := independent
  wardNamed := named

end YangMills.Matching.CorrelationOnly

