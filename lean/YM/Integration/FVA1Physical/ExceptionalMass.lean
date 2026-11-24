import YM.Integration.FVA1Physical.DensityComparison
import YM.MergeProof.South.Window
import YM.OPE.Therm.Law

/-! Size of an exceptional contribution after repeated physical blocking. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical

open MeasureTheory Lattice RG Wilson MergeProof.Accent

variable {G : Gauge} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded insertion at the fine cutoff stays bounded relative to the literal pushed
vacuum, at every coarse field and all intermediate scales. -/
theorem gust_vacuum_bound (H : History G) (h : H.Selected) (N p : ℕ)
    (seed : Config G (H.S.side N p) → E) (B : ℝ)
    (hseed : ∀ U, ‖((H.rep N p N).eval U)⁻¹ • seed U‖ ≤ B)
    (m : ℕ) (hm : m ≤ N) (V : Config G (H.S.side m p)) :
    ‖((H.rep N p m).eval V)⁻¹ • gust H N p N seed m hm V‖ ≤ B := by
  induction hm using Nat.decreasingInduction with
  | self => rw [gust_base]; exact hseed V
  | of_succ k hk ih =>
    rw [gust_step H N p N seed hk, ← conditionalPush_normalized H h N p k hk]
    exact conditionalPush_bound H h N p k hk _ B ih V

/-- The norm of a restricted, partition-normalized, transported reading is at most its
fine insertion bound times the actual coarse probability of that event. This applies to
a localized flag event as well as to the complement of the all-healthy sector. -/
theorem gust_event_bound (H : History G) (h : H.Selected) (N p : ℕ)
    (seed : Config G (H.S.side N p) → E) (B : ℝ)
    (hseed : ∀ U, ‖((H.rep N p N).eval U)⁻¹ • seed U‖ ≤ B)
    (m : ℕ) (hm : m ≤ N) (bad : Set (Config G (H.S.side m p))) (hb : MeasurableSet bad) :
    ‖∫ V in bad, gust H N p N seed m hm V ∂prior G (H.S.side m p)‖ /
        partition G (H.S.side N p) (H.β N p N) ≤
      B * (OPE.Therm.scene H N p m).real bad := by
  let μ := prior G (H.S.side m p)
  let ν := OPE.Therm.scene H N p m
  let w := (H.rep N p m).eval
  let Z := partition G (H.S.side N p) (H.β N p N)
  have hZ : 0 < Z := partition_pos _
  letI : IsProbabilityMeasure ν := OPE.Therm.probability h hm
  have hw : Integrable w μ := ((H.rep N p m).envelope (h.represents N p m hm).good).integrable _
  have bound (V) : ‖gust H N p N seed m hm V‖ ≤ w V * B := by
    have hp : 0 < w V := SectorNext.Vacuum.strictly H h N p m hm V
    have he := gust_vacuum_bound H h N p seed B hseed m hm V
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)] at he
    exact (inv_mul_le_iff₀ hp).mp he
  have normBound : ‖∫ V in bad, gust H N p N seed m hm V ∂μ‖ ≤ (∫ V in bad, w V ∂μ) * B := by
    rw [← integral_mul_const]
    exact norm_integral_le_of_norm_le ((hw.mul_const B).integrableOn) (Filter.Eventually.of_forall bound)
  have mass : (∫ V in bad, w V ∂μ) / Z = ν.real bad := by
    let χ := bad.indicator (fun _ => (1 : ℝ))
    have hχ : (∫ V, χ V ∂ν) = ν.real bad := by
      simp [χ, integral_indicator hb, measureReal_def]
    rw [OPE.Therm.account h hm χ] at hχ
    have eval : (fun V => OPE.Therm.dose (H := H) (p := p) m V N • χ V) =
        bad.indicator (fun V => w V / Z) := by
      funext V
      by_cases hv : V ∈ bad <;> simp [χ, hv, OPE.Therm.dose, w, Z]
    rw [eval, integral_indicator hb, integral_div] at hχ
    exact hχ
  change _ / Z ≤ B * ν.real bad
  rw [← mass]
  exact (div_le_div_of_nonneg_right normBound hZ.le).trans_eq (by ring)

end YM.Integration.FVA1Physical
