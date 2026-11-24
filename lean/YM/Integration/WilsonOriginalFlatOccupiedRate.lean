import YM.Integration.WilsonOriginalFlatOccupiedFace
import YM.Integration.WilsonFullFaceSignedHalo
import YM.Integration.WilsonCenteredCompleteFare

/-! Price the original hard part using each occupied source radius once. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatOccupiedRate
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Source
open WilsonCenteredMaskPieces WilsonCapturedPrimarySoftPartition WilsonCenteredMixedSetFiling
open WilsonFullFaceSignedHard
open scoped BigOperators Classical
open private YM.Integration.WilsonFullFaceSignedHalo.joint from YM.Integration.WilsonFullFaceSignedHalo

variable {n : Side} {V : Type} [DecidableEq V] {J : Census V}

def roof (p : BudgetPoint) (Z : Support n) (C : ℝ) (r : ℕ) : ℝ :=
  ((2^(2^r):ℕ):ℝ)*Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*(max 1 C)^r

private theorem blank (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (hw : ∀v,0<w v)
    {r : ℕ} (t : J.Mode) (load : t.val.card≤r) {E : ℝ} (ep : 0≤E) :
    0≤Poly.toll w t*WilsonCapturedPrimarySoftInventory.fare p Z w E t ∧
    Poly.toll w t*WilsonCapturedPrimarySoftInventory.fare p Z w E t≤roof p Z E r := by
  unfold WilsonCapturedPrimarySoftInventory.fare
  rw [mul_sum]
  have h (q : (parts J).Mode) (hq : q∈shards J t) := YM.Integration.WilsonFullFaceSignedHalo.joint w t q hq hw p Z E
  have lim (q : (parts J).Mode) (hq : q∈shards J t) :
      Poly.toll w t*tariff p Z w E q≤Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*(max 1 E)^r := by
    rw [h q hq]
    exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ ep (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) ((WilsonCapturedPrimarySoftLoad.size hq).trans load))) (Real.exp_nonneg _)
  constructor
  · exact sum_nonneg fun q hq=>by rw [h q hq];positivity
  · have cnt := (WilsonCapturedPrimarySoftLoad.count t).trans
          (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) load))
    exact (sum_le_sum lim).trans (by
      simp only [sum_const,nsmul_eq_mul,roof]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr cnt)
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)))

def bill (p : BudgetPoint) (Z : Support n) (E : ℝ) (r : ℕ) :=
  (2:ℝ)^r*(2*roof p Z E r*r*Real.exp r)

theorem earned (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (hw : ∀v,0<w v)
    (s : J.Mode) {r : ℕ} (load : s.val.card≤r) {E κ v : ℝ} (ep : 0≤E)
    (div : 0<κ) (small : κ≤1) (room : hitWidth p*v≤1) :
    Poly.toll w s*fee p Z w s E κ v κ≤bill p Z E r := by
  let row (t:J.Mode) := WilsonCapturedPrimarySoftInventory.fare p Z w E t
  have seen (z : J.Mode×J.Mode) (ok : z∈occupied s) :
      Poly.toll w s*((1+hitWidth p*v)*price (row z.1) w z.2 κ/κ)≤2*roof p Z E r*r*Real.exp r := by
    have both:=valid (mem_filter.mp ok).1
    have hl : z.1.val⊆s.val := both.2 ▸ subset_union_left
    have hr : z.2.val⊆s.val := both.2 ▸ subset_union_right
    have pair : Poly.toll w s=Poly.toll w z.1*Poly.toll w z.2 := by
      unfold Poly.toll; rw [←both.2,prod_union both.1]
    have ⟨pos,bound⟩:=blank p Z w hw z.1 ((card_le_card hl).trans load) ep
    have paid := WilsonCenteredCompleteFare.forced (t:=z.2) p (fun _=>1) (fun _=>zero_lt_one)
      div small room pos bound (show (Poly.toll (fun _:V=>1) z.2)⁻¹≤(1:ℝ) by simp [Poly.toll])
      ((card_le_card hr).trans load)
    calc
      _ = ((Poly.toll w z.1*row z.1)*(Real.exp (z.2.val.card*κ)-1)+
          hitWidth p*v*((Poly.toll w z.1*row z.1)*(Real.exp (z.2.val.card*κ)-1)))/κ := by
        rw [pair]
        unfold price
        field_simp [(Poly.worth hw z.2).ne',div.ne']

      _ ≤ _ := by simpa only [price,Poly.toll,prod_const_one,inv_one,one_mul,mul_one] using paid
  unfold fee bill
  rw [mul_sum]
  have b0 : 0≤roof p Z E r :=by unfold roof;positivity
  have cnt: (occupied s).card≤2^r := (card_le_card (filter_subset ..)).trans
    ((size s).trans (Nat.pow_le_pow_right (by decide) load))
  exact (sum_le_sum seen).trans (by
    simp only [sum_const,nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast cnt)

end YM.Integration.WilsonOriginalFlatOccupiedRate
