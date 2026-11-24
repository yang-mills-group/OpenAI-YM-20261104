import YM.RG05Readout.Pulse.Groups

/-! The actual joint smooth test at the translated children of one Wilson block.
The finite Taylor jet keeps all correlated directions of the reporting profile. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingCellTaylorRemainder
open Function Filter Set RG05Readout RG05Readout.Native RG05Readout.Pulse
open scoped Topology ContDiff BigOperators Classical
variable {I : Type*} [Fintype I]

def ray (φ : Wave I) (y v : Cloud I) (s : ℝ) : ℂ := φ.val (y+s • v)

def jet (φ : Wave I) (k : ℕ) (y v : Cloud I) (s : ℝ) : ℂ :=
  ∑ j∈Finset.range (k+1), (((j.factorial:ℝ)⁻¹*s^j) • iteratedDeriv j (ray φ y v) 0)

private theorem derivatives (φ : Wave I) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : (Cloud I × Cloud I) × ℝ => iteratedDeriv k (ray φ p.1.1 p.1.2) p.2) := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero,ray]
    exact (show ContDiff ℝ ∞ φ.val from φ.property).comp (by fun_prop)
  | succ k ih =>
    let D (v : Cloud I × Cloud I) (s : ℝ) := iteratedDeriv k (ray φ v.1 v.2) s
    simp_rw [iteratedDeriv_succ]
    change ContDiff ℝ ∞ (fun p : (Cloud I × Cloud I) × ℝ=> fderiv ℝ (D p.1) p.2 1)
    apply ContDiff.clm_apply (ContDiff.fderiv (n:=∞) (m:=∞)
      (f:=fun p : (Cloud I × Cloud I) × ℝ=>D p.1) (g:=Prod.snd) _ contDiff_snd (by simp)) contDiff_const
    exact ih.comp (f:=fun p : ((Cloud I × Cloud I) × ℝ) × ℝ => (p.1.1,p.2)) (by fun_prop)

theorem original (φ : Wave I) (K : Set (Cloud I)) (compact : IsCompact K) (k : ℕ) :
    ∃ A:ℝ, 0≤A ∧ ∀ y∈K, ∀ v:Cloud I, (∀ i,v i∈Native.box) →
      ∀ s:ℝ, 0<s → s≤1 → ‖φ.val (y+s • v) - jet φ k y v s‖ ≤ A*s^(k+1) := by
  let directions : Set (Cloud I) := Set.univ.pi (fun _=>Native.box)
  have compactV : IsCompact directions := isCompact_univ_pi (fun _=>Pert.Cellular.cells_compact)
  let sample (p : (Cloud I × Cloud I) × ℝ) := iteratedDeriv (k+1) (ray φ p.1.1 p.1.2) p.2
  obtain ⟨B,bank⟩:=((compact.prod compactV).prod (isCompact_Icc (a:=(0:ℝ)) (b:=1))).exists_bound_of_continuousOn
    (f:=sample) (derivatives φ (k+1)).continuous.continuousOn
  refine ⟨max 0 B,le_max_left ..,?_⟩
  intro y hy v hv s hs sh
  have vmem:v∈directions:=fun i _=>hv i
  have smooth:ContDiff ℝ ∞ (ray φ y v):=(show ContDiff ℝ ∞ φ.val from φ.property).comp
    (contDiff_const.add (contDiff_id.smul contDiff_const))
  have atOrder (j:ℕ) (x:ℝ) : ContDiffAt ℝ j (ray φ y v) x :=
    (smooth.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have inside (x:ℝ) (hx:x∈Icc 0 s) : ‖iteratedDerivWithin (k+1) (ray φ y v) (Icc 0 s) x‖ ≤ max 0 B := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs) (atOrder _ _) hx]
    exact (bank ((y,v),x) ⟨⟨hy,vmem⟩,hx.1,hx.2.trans sh⟩).trans (le_max_right ..)
  have h₀:(0:ℝ)∈Icc 0 s:=⟨le_rfl,hs.le⟩
  have eqn:taylorWithinEval (ray φ y v) k (Icc 0 s) 0 s=jet φ k y v s:=by
    rw [taylor_within_apply,jet]
    simp only [sub_zero]
    refine Finset.sum_congr rfl (fun j _=>?_ )
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hs) (atOrder _ _) h₀]
  change ‖ray φ y v s-jet φ k y v s‖≤_
  rw [←eqn]
  have h:=taylor_mean_remainder_bound hs.le
    (show ContDiffOn ℝ (k+1) (ray φ y v) (Icc 0 s) from fun x _=>(atOrder _ x).contDiffWithinAt)
    (show s∈Icc 0 s from ⟨hs.le,le_rfl⟩) inside
  rw [sub_zero] at h
  exact h.trans (div_le_self (mul_nonneg (le_max_left ..) (pow_nonneg hs.le _)) (by exact_mod_cast Nat.factorial_pos k))

end YM.Integration.WilsonReportingCellTaylorRemainder
