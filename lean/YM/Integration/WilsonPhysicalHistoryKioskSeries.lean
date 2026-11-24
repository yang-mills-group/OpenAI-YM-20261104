import YM.Integration.WilsonPhysicalHistoryKioskHeatOrder

/-! The surplus of four powers of the actual receiving coupling pays the
chronological sum of the signed rough insertions on every finite interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskSeries
open Function Filter Set Finset Lattice Wilson RG WilsonStartup RG.Shoot OPE.Therm Push.AbsoluteSums.Animals
open MeasureTheory IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "g" => regulatorRun R.family
local notation "hβ" => R.family.path.levels.clock.hatBeta

include simple in
/-- The original schedule buys at least a fixed positive beta increment
on each date, independently of all marked sources. -/
private theorem calendar : ∃ K : ℝ, 0<K ∧ ∀ i : ℕ,
    ((i:ℝ)+1)*((i:ℝ)+2) ≤ K*(hβ i)^2 := by
  let step := G.slopeConstant*Real.log 2
  let δ := min 1 step
  have gain : 0<step := mul_pos (Gauge.slopeConstant_pos simple) (Real.log_pos (by norm_num))
  have ep : 0<δ := lt_min zero_lt_one gain
  have advance (i : ℕ) : hβ i + δ ≤ hβ (i+1) := by
    have hi : (2:ℝ)≤(R.family.path.levels.S.block i).val := by
      have h:=R.family.path.levels.S.block_large i
      exact_mod_cast (by omega : 2 ≤ (R.family.path.levels.S.block i).val)
    have log := Real.log_le_log (by norm_num : (0:ℝ)<2) hi
    change R.family.path.levels.clock.bar+G.slopeConstant*R.family.path.levels.S.scale i+δ ≤ R.family.path.levels.clock.bar+G.slopeConstant*R.family.path.levels.S.scale (i+1)
    rw [Schedule.scale_succ]
    nlinarith only [min_le_right (1:ℝ) step,mul_le_mul_of_nonneg_left log (Gauge.slopeConstant_pos simple).le,
      (show δ≤G.slopeConstant*Real.log 2 from min_le_right _ _)]
  have one (i : ℕ) : δ*((i:ℝ)+1) ≤ hβ i := by
    induction i with
    | zero => simpa only [Nat.cast_zero,zero_add,mul_one] using
        ((min_le_left (1:ℝ) step).trans (R.family.path.levels.fits.delayed 0).le)
    | succ i ih =>
      push_cast
      nlinarith only [ih,advance i]
  refine ⟨2/δ^2,div_pos (by norm_num) (pow_pos ep _),?_⟩
  intro i
  have hb := (R.family.path.levels.fits.delayed i).le
  have left : (i:ℝ)+1 ≤ hβ i/δ := (le_div_iff₀ ep).mpr (by simpa [mul_comm] using one i)
  have right : (i:ℝ)+2 ≤ 2*hβ i/δ := (le_div_iff₀ ep).mpr
    (by nlinarith only [one i,(show δ≤1 from min_le_left _ _),hb])
  calc
    _ ≤ (hβ i/δ)*(2*hβ i/δ) := mul_le_mul left right (by positivity) (by positivity)
    _ = _ := by ring

include simple in
/-- The same upper cutoff controls both beta records. -/
theorem income (q : ℕ) : ∃ K : ℝ, 0<K ∧ ∀ k i N per : ℕ, k ≤ i → i≤N →
    (g N per i)^(q+4)*(((i:ℝ)+1)*((i:ℝ)+2)) ≤ K*(g N per k)^q := by
  obtain ⟨L,lp,one⟩:=calendar R simple
  refine ⟨2^q*4*L,by positivity,?_⟩
  intro k i N per ki hi
  let β := (R.family.path.rep N per i).beta
  let χ := (R.family.path.rep N per k).beta
  have bi : β∈Set.Icc (hβ i/2) (2*hβ i) := (R.makes.wilson.represents N per i hi).band
  have bk : χ∈Set.Icc (hβ k/2) (2*hβ k) := (R.makes.wilson.represents N per k (ki.trans hi)).band
  have hp := lt_trans zero_lt_one (R.family.path.levels.fits.delayed i)
  have bp : 0<β := (half_pos hp).trans_le bi.1
  have cp : 0<χ := (half_pos (lt_trans zero_lt_one (R.family.path.levels.fits.delayed k))).trans_le bk.1
  have clock := Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le ki
  have sg := Real.sqrt_pos.2 bp
  have sc := Real.sqrt_pos.2 cp
  have sq : Real.sqrt χ ≤ 2*Real.sqrt β := by
    apply (sq_le_sq₀ sc.le (by positivity)).mp
    nlinarith [Real.sq_sqrt cp.le,Real.sq_sqrt bp.le,bi.1,bk.2,clock]
  have relative : g N per i ≤ 2*g N per k := by
    change (Real.sqrt β)⁻¹ ≤ 2*(Real.sqrt χ)⁻¹
    simpa [one_div,div_eq_mul_inv] using (div_le_div_iff₀ sg sc).mpr (by simpa using sq : 1*Real.sqrt χ≤2*Real.sqrt β)
  have small : (g N per i)^4*(hβ i)^2 ≤ 4 := by
    change ((Real.sqrt β)⁻¹)^4*(hβ i)^2 ≤ 4
    rw [inv_pow,show (Real.sqrt β)^4=((Real.sqrt β)^2)^2 by ring,Real.sq_sqrt bp.le,←div_eq_inv_mul,
      div_le_iff₀ (pow_pos bp _)]
    nlinarith [mul_self_le_mul_self hp.le (by linarith [bi.1] : hβ i≤2*β)]
  have pi : 0≤g N per i := (inv_pos.mpr sg).le
  have pk : 0≤g N per k := (inv_pos.mpr sc).le
  have bound : (g N per i)^4*(((i:ℝ)+1)*((i:ℝ)+2)) ≤ 4*L := by
    calc
      _ ≤ (g N per i)^4*(L*(hβ i)^2) := mul_le_mul_of_nonneg_left (one i) (pow_nonneg pi _)
      _ = L*((g N per i)^4*(hβ i)^2) := by ring
      _ ≤ L*4 := mul_le_mul_of_nonneg_left small lp.le
      _ = _ := mul_comm _ _
  calc
    _ = (g N per i)^q*((g N per i)^4*(((i:ℝ)+1)*((i:ℝ)+2))) := by rw [pow_add,mul_assoc]
    _ ≤ (2*g N per k)^q*(4*L) :=
      mul_le_mul (pow_le_pow_left₀ pi relative _) bound (by positivity) (by positivity)
    _ = _ := by rw [mul_pow];ring

/-- Any finite collection of true dates costs at most one unit, regardless
of how far above the receiving date the original cutoff lies. -/
theorem installments (s : Finset ℕ) :
    ∑ i∈s, (1:ℝ)/(((i:ℝ)+1)*((i:ℝ)+2)) ≤ 1 := by
  let bill := fun i : ℕ => (1:ℝ)/(((i:ℝ)+1)*((i:ℝ)+2))
  have partialBill (k : ℕ) : ∑ i∈Finset.range k,bill i=1-1/((k:ℝ)+1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ,ih]
      dsimp only [bill]
      push_cast
      field_simp
      ring
  let n := s.sup id+1
  have sub : s⊆Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=id) hi))
  change ∑ i∈s,bill i ≤ 1
  calc
    _ ≤ ∑ i∈Finset.range n,bill i := Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => by
      dsimp [bill];positivity)
    _ = 1-1/((n:ℝ)+1) := partialBill n
    _ ≤ _ := sub_le_self _ (by positivity)

end YM.Integration.WilsonPhysicalHistoryKioskSeries
end
