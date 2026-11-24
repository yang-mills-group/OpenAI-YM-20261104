import YM.Integration.WilsonCenteredFiledGallery

/-! The two compulsory faces in the compensated pair are one sum over the
admissible original configurations. Each marked owner keeps every other
selected hard factor and its original signed vacuum weight. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompulsoryOwners
open Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Fusion.Attached Ac Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}

theorem grouped (A : Gallery X ι o P R) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    {α κ : ℝ} (width : 0 ≤ α) (spent : A.K.Paid w P.p.B α κ) (a b : V)
    (u v : ℂ) (x : X) (U : Config G n) :
    u*(A.gas x U).part (R.fire b) + (A.gas x U).part (R.fire a)*v =
      ∑' F : Finset ℕ, if P.activities.admissible P.p U F then
        ∑ i ∈ F, (u*(A.K.hard x i U).part (R.fire b) +
             (A.K.hard x i U).part (R.fire a)*v) *
          ∏ j ∈ F.erase i, (P.activities.K j U : ℂ)
        else 0 := by
  let p := packet P.activities P.p (A.K.hard x) U
  have total : Summable p := A.K.packet_summing spent width hw x U
  have face (c : V) : Summable (fun F => (p F).part (R.fire c)) :=
    ((Poly.get (R.fire c)).hasSum total.hasSum).summable
  rw [Gallery.gas, Poly.share total, Poly.share total, ←tsum_mul_left, ←tsum_mul_right,
    ←Summable.tsum_add ((face b).mul_left u) ((face a).mul_right v)]
  apply tsum_congr
  intro F
  by_cases h : P.activities.admissible P.p U F
  · simp only [p, packet, if_pos h, Multi.first_of_prod, A.K.quiet, Finset.mul_sum,
      Finset.sum_mul, ←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros
    ring
  · simp [p, packet, h]

/-- The cost attaches to a named hard owner on its actual support. It keeps
the once-divided κ and uses each fine regular singleton at its own radius. -/
theorem rooted (D : Lamps X ι G P.p o R)
    (K : Hard X P.p P.activities.forced P.activities.K o R)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) {α δ κ : ℝ} (width : 0 ≤ α)
    (regular : D.Paid w P.p.B α δ) (spent : K.Paid w P.p.B α κ) (a b : V)
    (x : X) (U : Config G n) :
    let u := (D.log x U).part (R.fire a)
    let v := (D.log x U).part (R.fire b)
    let r := ((w a)⁻¹*δ)*(w b)⁻¹ + (w a)⁻¹*((w b)⁻¹*δ)
    Hit (fun i => (P.activities.forced i).support) P.p.B (fun i =>
      ‖u*(K.hard x i U).part (R.fire b)+(K.hard x i U).part (R.fire a)*v‖) α (r*κ) := by
  intro u v r
  obtain ⟨g, covered, cap⟩ := spent.wages
  have E (c : V) : ‖(D.log x U).part (R.fire c)‖ ≤ (w c)⁻¹*δ := by
    simpa only [Poly.toll, Census.fire, prod_singleton] using
      WilsonCenteredRegularHit.component D w hw width regular x U (R.fire c) c (mem_singleton_self c)
  have H (i : ℕ) (c : V) :
      ‖(K.hard x i U).part (R.fire c)‖ ≤ (w c)⁻¹ * Poly.price w (g i) := by
    have bill := (Poly.member hw (R.fire c) (K.hard x i U)).trans ((covered i x U).reprice w hw)
    simp only [Poly.toll, Census.fire, prod_singleton] at bill
    apply (le_of_mul_le_mul_left ?_ (hw c))
    simpa only [Census.fire, ←mul_assoc, mul_inv_cancel₀ (hw c).ne', one_mul] using bill
  have dpos (c : V) : 0 ≤ (w c)⁻¹*δ := (norm_nonneg _).trans (E c)
  have rpos : 0 ≤ r := add_nonneg (mul_nonneg (dpos a) (inv_nonneg.mpr (hw b).le))
    (mul_nonneg (inv_nonneg.mpr (hw a).le) (dpos b))
  have atom (i : ℕ) : ‖u*(K.hard x i U).part (R.fire b)+(K.hard x i U).part (R.fire a)*v‖ ≤
      r * Poly.price w (g i) := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_mul]
    have ha := mul_le_mul (E a) (H i b) (norm_nonneg _) (dpos a)
    have hb := mul_le_mul (H i a) (E b) (norm_nonneg _)
      (mul_nonneg (inv_nonneg.mpr (hw a).le) (Poly.nonnegative hw _))
    dsimp [u,v,r]
    apply (add_le_add ha hb).trans_eq
    ring
  intro y
  refine budget_mono (budget_scale rpos (cap y)) (fun i => ?_) (fun i => ?_)
  · split_ifs
    · positivity
    · exact le_rfl
  · by_cases h : y ∈ (P.activities.forced i).support
    · simp only [if_pos h, ←mul_assoc]
      exact mul_le_mul_of_nonneg_right (atom i) (Real.exp_pos _).le
    · simp [h]

end YM.Integration.WilsonCenteredCompulsoryOwners
