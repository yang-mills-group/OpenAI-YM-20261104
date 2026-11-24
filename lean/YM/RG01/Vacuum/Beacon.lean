import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Revenue

/-!
# RG01. The strong graded log moment

Rather than spending both exponential reserves on the older cubic grade,
retain the entire beacon weight on the log polynomial. This is an
arity (incl. correction horns), seed and path-depth weight; it is not
the Lie-field Taylor grade or a purported global coupling holomorphy.
At the actual Cash output this makes it possible to do all the remaining
Taylor analyses at *fixed finite arity*, without trying to use rescaled
perturbative Taylor factors in the seed estimates (esp. in the held
variable/score integrals). See also Census/Revenue and /Widow.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext Repeat Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ} {k j n : ℕ}
    {χ : Chi} {H : Cash W s μ L Q o α T R}

variable (N : Captain H j C' d v Y A b r B q k χ) (hd : 1 ≤ grow G L s) (hh' : Heavy N.conduit)
variable (n : ℕ) (ht : Armada Q L μ a s i B j k)
local notation "D" => grow G L s
include hd hh' ht

/-- The full beacon exponential moment of the **absolute values** of the E6
unforced-log derivative envelopes. Uniform in all tori and choices meeting
these actually purchasable pre-L and post-L prices. Includes arbitrary fixed
power index n (bought on the actual steps up to budget powers, see Purchase). -/
theorem beaconMoment
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (D*salary Q L μ B s j k) i ≤ 1/2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s)
      (fun z=> beacon H z * N.markΦ z n) a
      (collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  intro x
  have hy:= log_hit_tail _ _ _ H.testS (stable N hd hh' i a ht.delta ht.little ht.earned hs hp) (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero,mul_one] at hy
  have he:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hv:0 ≤ collars G i s j n:=by unfold collars Reserves.polyPrice; have := ht.delta; positivity
  have hD:0<D:=zero_lt_one.trans_le hd
  have hm z : 0 ≤ beacon H z := by unfold beacon; positivity
  have hz z : 0 ≤ N.markΦ z n:= mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  have hh:= budget_scale hv hy
  refine budget_mono hh (fun z=> ?_) fun z=> ?_
  · dsimp only; split_ifs
    next => exact mul_nonneg (mul_nonneg (hm _) (hz _)) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split
  next hx=>
    rw [if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),wield N]
    let u:ℝ:=coverNumber (radiusB s) (Captain.reachability (H:=H) z); have hg:0 ≤ u:= Nat.cast_nonneg _
    change beacon H z * ((shiftG s*(1+u))^(n*j)*N.design z) *Real.exp (a*u) ≤ _ * (beacon H z*N.design z * Real.exp ((a+i)*u))
    have hc : (shiftG s*(1+u))^(n*j) * Real.exp (a*u) ≤ collars G i s j n * Real.exp ((a+i)*u) := by
      rw [mul_pow]; unfold collars
      calc
        _ ≤ (shiftG s ^ (n*j) * (polyPrice i (n*j)*Real.exp (i*u)))*Real.exp (a*u) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg he _)
          exact polynomial_cost ht.delta hg _
        _ = _ := by rw [add_mul, Real.exp_add]; ring
    calc
      _ = beacon H z*N.design z * ((shiftG s*(1+u))^(n*j)*Real.exp (a*u)) := by ring
      _ ≤ beacon H z*N.design z * (collars G i s j n * Real.exp ((a+i)*u)) := mul_le_mul_of_nonneg_left hc (mul_nonneg (hm _) (N.pvc _))
      _ = _ := by ring
  exact hh.1 z

variable (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)

include N hs hp
/-- Pick any exceptional log-component population, pay the *inverse* of its
already present beacon reserve. This is on complete supports at the same
Budgets, not a pointwise Taylor estimate. -/
theorem beaconTail (take : H.fragrances → Prop) (w : ℝ) (hw : 0 < w)
    (he : ∀ z, take z → w ≤ beacon H z) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z => if take z then N.markΦ z n else 0) a
      (w⁻¹*(collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  have hT := beaconMoment N hd hh' n ht hs hp
  have hD:0<D:=zero_lt_one.trans_le hd
  intro x
  have hQ:=budget_scale (inv_nonneg.mpr hw.le) (hT x)
  have hz z : 0 ≤ N.markΦ z n:= by
    have he:0 ≤ shiftG s:= by unfold shiftG; positivity
    exact mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  have hm z:0≤beacon H z := by unfold beacon; positivity
  refine budget_mono hQ (fun z => ?_) fun z => ?_
  · dsimp only; split
    next hx =>
      split
      next ht' => exact mul_nonneg (hz _) (Real.exp_pos _).le
      simp
    exact le_rfl
  dsimp only; split
  next hx =>
    by_cases hg:take z
    · rw [if_pos hg]
      rw [show w⁻¹*(beacon H z*N.markΦ z n * Real.exp _)= (w⁻¹*beacon H z)*(N.markΦ z n*Real.exp (a* coverNumber (radiusB s) (Captain.reachability z))) by ring]
      apply le_mul_of_one_le_left (mul_nonneg (hz z) (Real.exp_pos _).le)
      rw [mul_comm, ← div_eq_mul_inv]; exact (one_le_div hw).2 (he z hg)
    rw [if_neg hg,zero_mul]
    exact mul_nonneg (inv_nonneg.mpr hw.le) (mul_nonneg (mul_nonneg (hm z) (hz z)) (Real.exp_pos _).le)
  rw [mul_zero]

omit N hh' hs hp ht
include H hd
lemma beacon_ge (z : H.fragrances) : D ^ degree H z ≤ beacon H z := by
  have hD : 0≤ D := zero_le_one.trans hd
  apply le_trans (le_mul_of_one_le_right (pow_nonneg hD (degree H z)) (b:=Real.exp (Q.mark L μ s*overlap H z)) ?_)
    (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (mul_nonneg Q.usable.le
        (sum_nonneg fun _ _=> H.positive_volume _))))
  exact Real.one_le_exp (mul_nonneg H.laws.acquired.marked (Nat.cast_nonneg _))

include N hh' hs hp ht
/-- All-order arity tail, no seed/path purchase beyond that already in the
full beacon hypotheses. Use arity > perturbative order in applications,
since `grow` is at g to the minus 3/4, NOT minus one. -/
theorem logDegreeTail (p : ℕ) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z => if p ≤ degree H z then N.markΦ z n else 0) a
      ((D^p)⁻¹*(collars G i s j n*(D*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  let t z := p ≤ degree H z
  have h := beaconTail N hd hh' n ht hs hp t (D^p) (pow_pos (zero_lt_one.trans_le hd) _) (fun z h =>
    le_trans (pow_le_pow_right₀ hd h) (beacon_ge hd z))
  classical  -- need convert via Subsingleton.elim
  convert! h using 1
  ext z
  dsimp only [t]; split <;> simp [*]

end YM.RG01.Vacuum
