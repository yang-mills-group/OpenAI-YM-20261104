import YM.Integration.WilsonCenteredCompulsoryCollection

/-! Issue the joint regular and hard address invoice before sampling either
the physical group field or the common test. The wage functions are the
same ones used by the original marked hard and regular ledgers. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredHardEnvelope
open Finset Lattice RG Wilson Marker QuadraticLocal Ac Corona Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι μ : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}
variable (D : Lamps X ι G P.p o R) (A : Gallery X μ o P R)
    (w : V → ℝ) (hw : ∀ v, 0 < w v) {α δ κ : ℝ} (width : 0 ≤ α)
    (regular : D.Paid w P.p.B α δ) (hard : A.K.Paid w P.p.B α κ)

include hw width regular hard

private theorem prefield (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z) :
    ∃ e : ι × ℕ → ℝ,
      (∀ z, 0 ≤ e z) ∧
      (∀ (x : X) (U : Config G n) (z : ι × ℕ),
        (w a*‖(D.frame z.1 x U).part (R.fire a)‖) *
        (w b*‖(A.K.hard x z.2 U).part (R.fire b)‖) ≤ e z) ∧
      SumBudget (fun z => e z * Real.exp (α*coverNumber P.p.B
        (D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support)))
        (Real.exp (α*coverNumber P.p.B Z)*(δ*κ)) := by
  classical
  obtain ⟨f,positive,caps,billed⟩ := regular.budget
  obtain ⟨g,covers,spent⟩ := hard.wages
  let F i := if o a ∈ D.ground i then Poly.toll w (D.mode i)*f i else 0
  let H i := if o b ∈ (P.activities.forced i).support then Poly.price w (g i) else 0
  have Fpos (i : ι) : 0 ≤ F i := by
    dsimp [F];split_ifs
    · exact mul_nonneg (Poly.worth hw _).le (positive _)
    · exact le_rfl
  have Hpos (i : ℕ) : 0 ≤ H i := by
    dsimp [H];split_ifs
    · exact Poly.nonnegative hw _
    · exact le_rfl
  have df (x : X) (U : Config G n) (i : ι) :
      w a*‖(D.frame i x U).part (R.fire a)‖ ≤ F i := by
    by_cases ha : o a ∈ D.ground i
    · simp only [F,if_pos ha]
      have included := Poly.member hw (R.fire a) (D.frame i x U)
      have cost : Poly.price w (D.frame i x U) ≤ Poly.toll w (D.mode i)*f i := by
        rw [Lamps.frame,Poly.solo]
        exact mul_le_mul_of_nonneg_left (D.light_size i x U (caps i x _ (D.address i).anchor))
          (Poly.worth hw _).le
      simpa only [Poly.toll,Census.fire,prod_singleton] using included.trans cost
    · have neq : R.fire a ≠ D.mode i := by
        intro eq
        apply ha
        apply D.roots i
        rw [←eq]
        exact mem_singleton_self _
      simp [F,ha,Lamps.frame,Poly.part_send,neq]
  have kh (x : X) (U : Config G n) (i : ℕ) :
      w b*‖(A.K.hard x i U).part (R.fire b)‖ ≤ H i := by
    by_cases hb : o b ∈ (P.activities.forced i).support
    · have included := (Poly.member hw (R.fire b) (A.K.hard x i U)).trans
          ((covers i x U).reprice w hw)
      simpa only [H,if_pos hb,Poly.toll,Census.fire,prod_singleton] using included
    · have zero : (A.K.hard x i U).part (R.fire b)=0 := by
        by_contra contrary
        exact hb ((A.K.locality x i).carry U _ contrary b (mem_singleton_self _))
      simp [H,hb,zero]
  refine ⟨fun z => F z.1*H z.2,fun z => mul_nonneg (Fpos _) (Hpos _),
    fun x U z => mul_le_mul (df x U z.1) (kh x U z.2)
      (mul_nonneg (hw b).le (norm_nonneg _)) (Fpos _),?_⟩
  let total := budget_scale (Real.exp_pos (α*coverNumber P.p.B Z)).le
    (budget_prod (billed (o a)) (spent (o b)))
  apply budget_mono total (fun z => mul_nonneg (mul_nonneg (Fpos _) (Hpos _)) (Real.exp_pos _).le)
  rintro ⟨i,j⟩
  by_cases ha : o a ∈ D.ground i
  · by_cases hb : o b ∈ (P.activities.forced j).support
    · have first := meets_sum ha za P.p.B
      have second := meets_sum (mem_union_right (D.ground i) zb) hb P.p.B
      have geo : coverNumber P.p.B (D.ground i ∪ Z ∪ (P.activities.forced j).support) ≤
          coverNumber P.p.B Z + coverNumber P.p.B (D.ground i) + coverNumber P.p.B (P.activities.forced j).support := by omega
      have geoR : (coverNumber P.p.B (D.ground i ∪ Z ∪ (P.activities.forced j).support) : ℝ) ≤
          (coverNumber P.p.B Z : ℝ) + coverNumber P.p.B (D.ground i) + coverNumber P.p.B (P.activities.forced j).support := by exact_mod_cast geo
      have strip := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left geoR width)
      simp only [mul_add,Real.exp_add] at strip
      refine (mul_le_mul_of_nonneg_left strip (mul_nonneg (Fpos i) (Hpos j))).trans_eq ?_
      simp only [F,H,if_pos ha,if_pos hb]
      ring
    · simp [H,hb]
  · simp [F,ha]

theorem original (a b : V) (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z) (hk : 0 < κ) :
    ∃ E : ι × ℕ → ℝ,
      (∀ z, 0 ≤ E z) ∧
      (∀ x U z, w a*w b*‖WilsonCenteredCompulsoryCollection.joint D A a b x U z.1 z.2‖ ≤ E z) ∧
      SumBudget (fun z => κ⁻¹ * (E z * Real.exp (α*coverNumber P.p.B
        (D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support))))
        (2*Real.exp (α*coverNumber P.p.B Z)*δ) := by
  obtain ⟨e,he,ae,paid⟩ := prefield D A w hw width regular hard a b Z za zb
  obtain ⟨f,hf,af,owed⟩ := prefield D A w hw width regular hard b a Z zb za
  refine ⟨fun z => e z+f z,fun z=>add_nonneg (he z) (hf z),?_,?_⟩
  · intro x U z
    have h := norm_add_le
      ((D.frame z.1 x U).part (R.fire a)*(A.K.hard x z.2 U).part (R.fire b))
      ((A.K.hard x z.2 U).part (R.fire a)*(D.frame z.1 x U).part (R.fire b))
    simp only [norm_mul] at h
    apply (mul_le_mul_of_nonneg_left h (mul_nonneg (hw a).le (hw b).le)).trans
    apply le_trans _ (add_le_add (ae x U z) (af x U z))
    apply le_of_eq
    ring
  · have bill := budget_scale (inv_pos.mpr hk).le (budget_plus paid owed)
    convert bill using 1
    · ext z
      rw [add_mul]
    · field_simp
      ring

end YM.Integration.WilsonCenteredHardEnvelope
