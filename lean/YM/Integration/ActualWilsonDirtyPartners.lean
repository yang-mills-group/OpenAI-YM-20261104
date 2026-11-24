import YM.Integration.ActualWilsonTouchingVacuum
import YM.Integration.ActualWilsonFailedMaskPrice
import YM.Push.ABSOLUTE_SUMS.Array

/-! Nonempty touching packets retain a power of the actual vacuum allowance.
The original Taylor stem pays the joint sum over rows and vacuum partners. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonDirtyPartners
open Function Finset Lattice RG Wilson Marker Source Labels
open Push.AbsoluteSums RG3.Forms RG3.Primary RG3.Press Push.Local Overlay
open ActualWilsonTouchingVacuum
open scoped BigOperators Classical
variable {ι : Type*} {G : Gauge} {n : Side}

theorem omit_one {f : ι → ℝ} {C : ℝ} (h : SumBudget f C) (base : ι) :
    SumBudget (fun j => if j ≠ base then f j else 0) (C-f base) := by
  apply budget_of_sum
  · intro j
    split
    · exact h.1 j
    exact le_rfl
  intro S
  rw [← Finset.sum_filter]
  have h0 : base ∉ S.filter (fun j => j ≠ base) := by simp
  have H := budget_sum h (insert base (S.filter (fun j => j ≠ base)))
  rw [Finset.sum_insert h0] at H
  linarith only [H]

theorem increment (x : ℝ) : Real.exp x-1 ≤ x*Real.exp x := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero _)] at h
  linarith only [h]

def blockSites (B : ℕ) : ℝ := (((B+B+1 : ℕ) : ℝ)^4)

def dirty (p : BudgetPoint) (D : ι → Support n) (Y : Support n) (b : ι → ℝ) (I : Finset ι) :=
  if I ≠ ∅ then invoice p D Y b I else 0

/-- One compulsory nonempty attaching set gains the small original allowance.
The support exponent pays all remaining attachments. -/
theorem native (W : Rep G n) {w : ℝ} (hW : W.activities.KBound W.p w)
    (hw : w*blockSites W.p.B ≤ 1/2) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j ∧ ∀ U, ‖W.activities.K j U‖ ≤ b j) ∧
      ∀ Y : Support n, SumBudget (dirty W.p (fun j => (W.activities.forced j).support) Y b)
        (2*(w*blockSites W.p.B)*Real.exp ((W.p.supportExponent+1)*coverNumber W.p.B Y)) := by
  obtain ⟨b,hb,hit⟩ := hW
  refine ⟨b,hb,fun Y => ?_⟩
  let D j := (W.activities.forced j).support
  let a := W.p.supportExponent
  let k : ℝ := coverNumber W.p.B Y
  let t := w*blockSites W.p.B
  let x : ℝ := Y.card*w
  have hw0 : 0 ≤ w := budget_nonneg (hit 0)
  have ht : 0 ≤ t := mul_nonneg hw0 (by unfold blockSites; positivity)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hx : 0 ≤ x := mul_nonneg (Nat.cast_nonneg _) hw0
  have hvol : x ≤ t*k := by
    have hs : (Y.card : ℝ) ≤ k*blockSites W.p.B := by
      dsimp only [k,blockSites]
      exact_mod_cast Corona.pays Y W.p.B
    dsimp only [x,t]
    calc _ ≤ (k*blockSites W.p.B)*w := mul_le_mul_of_nonneg_right hs hw0
         _ = _ := by ring
  have hxk : x ≤ k/2 := hvol.trans (by
    have hmul := mul_le_mul_of_nonneg_right hw hk
    change t*k ≤ _
    linarith only [hmul])
  have hhalf : k ≤ 2*Real.exp (k/2) := by linarith only [Real.add_one_le_exp (k/2)]
  have hsub : Real.exp x-1 ≤ 2*t*Real.exp k := by
    calc _ ≤ x*Real.exp x := increment x
         _ ≤ (t*k)*Real.exp (k/2) := mul_le_mul hvol (Real.exp_monotone hxk) (Real.exp_pos _).le (mul_nonneg ht hk)
         _ = t*(k*Real.exp (k/2)) := by ring
         _ ≤ t*((2*Real.exp (k/2))*Real.exp (k/2)) :=
             mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hhalf (Real.exp_pos _).le) ht
         _ = _ := by rw [mul_assoc 2,← Real.exp_add,show k/2+k/2=k by ring]; ring
  have H := omit_one (products W.p D Y (fun j => (hb j).1) hit) (∅ : Finset ℕ)
  have hempty : invoice W.p D Y b ∅ = Real.exp (a*k) := by simp [invoice,BudgetPoint.mass,a,k]
  rw [hempty] at H
  have H' : SumBudget (dirty W.p (fun j => (W.activities.forced j).support) Y b)
      (Real.exp (a*k+x)-Real.exp (a*k)) := by
    apply budget_mono H
    · intro j
      by_cases h : j = ∅
      · simp [dirty,h]
      · rw [dirty,if_pos h]
        exact (products W.p D Y (fun j => (hb j).1) hit).1 j
    · intro j
      by_cases h : j = ∅ <;> simp [dirty,D,h]
  apply budget_loosen H'
  change Real.exp (a*k+x)-Real.exp (a*k) ≤ 2*t*Real.exp ((a+1)*k)
  have h := mul_le_mul_of_nonneg_left hsub (Real.exp_pos (a*k)).le
  rw [show (a+1)*k=a*k+k by ring,Real.exp_add,Real.exp_add]
  linarith only [h]

/-- The complete paid native Taylor row sum, on the genuine original
coefficient table, has no slot or volume multiplier. -/
theorem stem {V : Type} [DecidableEq V] {B : Census V} {d : ℕ} {F : Frame G d}
    (W : Rep G n) {w : ℝ} (hW : W.activities.KBound W.p w) (hw : w*blockSites W.p.B ≤ 1/2)
    (v : V) (D : Deck B W) (A : Hol G) (sec : SectionData F) {r : ℝ}
    (he : Readable A sec W.p n r) {θ : V → ℝ} (hθ : ∀ v, 0 < θ v)
    {m : ℕ → ℝ} {s : ℝ} (H : StemPay v D A sec r θ m s) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j ∧ ∀ U, ‖W.activities.K j U‖ ≤ b j) ∧
      SumBudget (fun z : ℕ × Finset ℕ => θ v*ink (F := F) v D A r m z.1 *
        dirty W.p (fun j => (W.activities.forced j).support) (RG3.Primary.stem v D sec z.1) b z.2)
        (2*(w*blockSites W.p.B)*s) := by
  obtain ⟨b,hb,hstock⟩ := native W hW hw
  refine ⟨b,hb,?_⟩
  let t := 2*(w*blockSites W.p.B)
  let row j := θ v*gross v D A sec r m j
  have ht : 0 ≤ t := by
    have h0 : 0 ≤ w := budget_nonneg ((Classical.choose_spec hW).2 0)
    exact mul_nonneg (by norm_num) (mul_nonneg h0 (by unfold blockSites; positivity))
  apply budget_rows _ (fun j => t*row j) _ (budget_scale ht H.2)
  intro j
  have H' := budget_scale (mul_nonneg (hθ v).le (H.positive he j))
    (hstock (RG3.Primary.stem v D sec j))
  convert H' using 1
  dsimp only [t,row,gross]
  ring

end YM.Integration.ActualWilsonDirtyPartners
