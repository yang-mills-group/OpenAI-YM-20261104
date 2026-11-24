import YM.Integration.WilsonMacroscopicRichCommonFiling

/-! Compare two dated reports via one terminal field on the original capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichDoubleCurrency
open Filter Lattice Wilson RG Source Extra.Histories MergeProof Ribbons
open Trace.Physical.GermGraph RG16.Literal
open scoped Topology Classical BigOperators
variable {G : Gauge} (C : Family G) (H : C.Makes) (d : ℕ)

include H
private theorem triangle (N p b:ℕ) (opening:Opened C d b p) (live:b ≤ N) (x y a:C.label d) :
    mCost C d N p b (x-y) ≤ mCost C d N p b (x-a)+mCost C d N p b (y-a) := by
  let F:=C.labels.level d
  let f:=fitting d N p b H opening live
  change F.coeffSize (f (x-y)) ≤ F.coeffSize (f (x-a)) + F.coeffSize (f (y-a))
  have ident : f (x-y)=f (x-a)+ -(f (y-a)) := by rw [←map_neg,←map_add];congr 1;abel
  rw [ident]
  have neg : F.coeffSize (-f (y-a))=F.coeffSize (f (y-a)) := by
    unfold Labels.Frame.coeffSize
    apply Finset.sum_congr rfl
    intro i _
    exact norm_neg _
  exact (Size.add F (f (x-a)) (-f (y-a))).trans_eq (by rw [neg])

theorem priced (mat:Materials C) {γ:ℝ} (positive:0 < γ) (small:γ < 1/8) :
    ∀ᶠ v:ℕ in atTop, ∀ (u b N p:ℕ) (_:v ≤ u) (_:u ≤ b) (_:b ≤ N)
      (_:Opened C d b p) (E:ℝ) (_:0 ≤ E) (x y a:C.label d),
      mCost C d N p v (x-a) ≤ E/Bid.gainChart C.path b v →
      mCost C d N p u (y-a) ≤ E/Bid.gainChart C.path b u →
      mCost C d N p b (x-y) ≤ 2*E*Real.exp (-(1/8-γ)*(C.S.scale b-C.S.scale u)) := by
  obtain ⟨t,start⟩:=eventually_atTop.1 (WilsonMacroscopicRichCountertermAtCapture.forward C mat d positive)
  filter_upwards [eventually_ge_atTop t] with v tv
  intro u b N p vu ub live opening E hE x y a old current
  have transport (i:ℕ) (late:t ≤ i) (ib:i ≤ b) (w:C.label d)
      (price:mCost C d N p i w ≤ E/Bid.gainChart C.path b i) :
      mCost C d N p b w ≤ E*Real.exp (-(1/8-γ)*(C.S.scale b-C.S.scale i)) := by
    let s:=C.S.scale b-C.S.scale i
    calc
      _ ≤ Real.exp (γ*s)*mCost C d N p i w := start i late b ib N p live w
      _ ≤ Real.exp (γ*s)*(E/Bid.gainChart C.path b i) := mul_le_mul_of_nonneg_left price (Real.exp_pos _).le
      _ = E*(Real.exp (γ*s)*Real.exp (-(1/8*s))) := by
        change Real.exp (γ*s)*(E/Real.exp ((1/8)*s))=_
        rw [Real.exp_neg];ring
      _ = _ := by rw [←Real.exp_add];congr 2;dsimp [s];ring
  have first:=transport v tv (vu.trans ub) (x-a) old
  have second:=transport u (tv.trans vu) ub (y-a) current
  have step:(C.S.scale b-C.S.scale u) ≤ (C.S.scale b-C.S.scale v):=
    sub_le_sub_left ((OPE.scale_mono C.S).monotone vu) _
  have eps:=Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left step (neg_nonpos.mpr (sub_nonneg.mpr small.le)))
  exact (triangle C H d N p b opening live x y a).trans (by
    linarith only [first,second,mul_le_mul_of_nonneg_left eps hE])

end YM.Integration.WilsonMacroscopicRichDoubleCurrency
