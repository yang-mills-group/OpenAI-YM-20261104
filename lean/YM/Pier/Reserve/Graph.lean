import YM.Pier.Reserve.Difference
import YM.FullVolume.Mark.Prism
/-! The native Tool and Gram recurrence (this 'Gram' is of field columns,
**not** the reflected two-point matrix input to sharp OPE). For two
nearby stocks on ONE vacuum history, separate regular/forced input differences
in propagating the all-configuration column difference. In particular the
better cost on the forced input survives every address change through this
recipient and is now in the SAME norm as the physical field columns. Use
it as a small perturbation for the stable column recurrence (including the
inverse field-coordinate recalibration), with uniform costs noted below.
Adapted from Mark/{Booths,Carts,Purse}. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pier
open Finset Function Set Filter MeasureTheory Lattice Wilson RG Source Labels Bid
  Extra.Histories Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
  MergeProof MergeProof.Matric MergeProof.Matric.Gram
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G:Gauge} {d:ℕ} {F:Labels.Frame G d} {B:SectionData F} {H:History G} {N p j:ℕ} {Y:Hol G}
variable {W:Worth} {u ζ v C : ℝ}
variable {S:Desk G (H.S.side (j+1) p)} {E:Desk G (H.S.side j p)}
local notation "Old"=> H.rep N p (j+1)
local notation "Out"=> H.rep N p j
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance j)
local notation "κ'"=> Real.sqrt (H.levels.clock.forcedAllowance (j+1))
set_option quotPrecheck false
local notation "s" => (H.levels.params (j+1)).columns
local notation "s'" => (H.levels.params j).columns
local notation "o" => orbitCost F

/-- On **this Desk**. Includes off-trajectory inputs to the SAME Tool.
    `C` will include all further error prices of the actual comparison. -/
def InRange (H:History G) (N p j:ℕ) {S:Desk G (H.S.side (j+1) p)}
    (Q U:Gram F Y S ((H.levels.params (j+1)).columns)) (c:ℝ) : Prop :=
  ∀ i:F.Index, ∃ fE fK:ℝ,
    Tab (book (Size.axis F i) (Coin.uses (Q.scythe i-U.scythe i))) 0 (H.rep N p (j+1))
      (Real.sqrt (H.levels.clock.forcedAllowance (j+1))) fE fK ∧
    fE+Real.sqrt (H.levels.clock.forcedAllowance (j+1))*fK ≤ c*(H.levels.params (j+1)).columns

variable (P : Tool F H N p j) {D : GaugeDoor (H.rep N p (j+1)) (H.rep N p j)}
    {T : Heading F} {X : Set Wing} (h : Tool.Cap P B Y W D T u ζ v X)
    (hc : Lathe H N p j Y B (H.rep N p (j+1)) P.plate D u ζ)
    (hw : Well (H.rep N p (j+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (j+1))))
    (ha : Afford P.plate Y (H.rep N p (j+1)) (H.rep N p j))
    (Q U:Gram F Y S ((H.levels.params (j+1)).columns))
    (hy : InRange H N p j Q U C)
local notation "Z"=>ζ*(C*s)
local notation "Z'"=>(ζ*(C*s)*orbitCost F)
include h hc hw ha hy
lemma radians (i:Tally F) :
    let y:=breakP (P.portfolio Q.scythe i) (P.portfolio U.scythe i)
    y.Format 0 Y Out ∧ F.coeffSize y.x ≤ ζ*(C*s) ∧ Room y 0 Out κ 1 (ζ*(C*s)) := by
  intro y
  obtain ⟨a,b,hQ,hU⟩:= hy i.2
  have he := mul_le_mul_of_nonneg_left hU h.budget.epsilon
  let f:= breakP (P.shot i.2 (Coin.uses (Q.scythe i.2))) (P.shot i.2 (Coin.uses (U.scythe i.2)))
  obtain ⟨hf,hR⟩:= Slate.recoilDelta P h hw i.2 _ _ hc ha hQ
  obtain ⟨u,v,hv,hCost⟩:= hf.income
  let hside:2≤(H.S.side j p).val:= ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S j p))
  obtain ⟨heq,hx,hT,-⟩:= audition_receipt i.1 (P.whirl i.1) hside h.good hf.earns hv
  have hw' : y = audition (P.whirl i.1) f := (turn_br ..).symm
  rw [hw']; exact ⟨hx,heq.symm ▸ ((patch_cost ..).trans (hf.first.trans he)),
    (hR.auditioned i.1 (P.whirl i.1) hside h.good hf.earns).larger he⟩

/-- Sufficient allowance in the reset consumes the unchanged Loom precision. -/
def stepAllowance (F : Labels.Frame G d) (K : ℝ) (ζ C : ℝ) : ℝ :=
  ζ*(C*K)*orbitCost F

variable (hp : roomCost H.levels W) (hK:Bank W H.levels)
    (hl:Well (H.rep N p j) E (Real.sqrt (H.levels.clock.forcedAllowance j)))
include hp hK

lemma profilePoint (hC : 0 ≤ C) (x:F.Coeff) :
    let y:=breakP (Q.point P x) (U.point P x)
    let m:= stepAllowance F (H.levels.params (j+1)).columns ζ C * F.coeffSize x
    y.Format 0 Y Out ∧ F.coeffSize y.x ≤ m ∧ Room y 0 Out κ 1 m ∧
      y.density 0 B Out=(Q.point P x).density 0 B Out-(U.point P x).density 0 B Out := by
  intro y m
  let f (i:Tally F) := breakP (P.portfolio Q.scythe i) (P.portfolio U.scythe i)
  let g (i:Tally F) := chips F x i
  let v' : ℝ := (Z)
  let t := ∑ i:Tally F, ‖g i‖*v'
  have hs : 0 ≤ s := zero_le_one.trans (H.levels.params (j+1)).columns_ge
  have ht:t ≤ m := by
    unfold t; rw [← Finset.sum_mul]; exact (mul_le_mul_of_nonneg_right (rip F x)
      (mul_nonneg h.budget.epsilon (mul_nonneg hC hs))).trans_eq (by unfold m stepAllowance; ring)
  have hf(i):= radians P h hc hw ha Q U hy i
  have h₁: y = Extra.Histories.pencil (code _) f (chips F) x := (pencil_br ..).symm
  have HK : 0 < κ := Real.sqrt_pos.mpr (forcedPos ..)
  have hR : Room y 0 Out κ 1 t := by
    have hW:= Room.combine (code _) (le_refl (1:ℝ)) HK
      (fun i=>(hf i).2.2.weighted (g i)) Summable.of_finite
    rw [tsum_fintype] at hW
    rw [h₁]; exact hW
  refine ⟨?_,?_,hR.larger ht,?_⟩
  · rw [h₁]; exact (pencil_cost (code _) _ (chips F) HK
      (fun i=> ⟨(hf i).1,(hf i).2.2.conventional⟩) x).1
  · rw [h₁, pencil_x]; exact (Size.finite F _ _).trans ((Finset.sum_le_sum
      (fun i _=>(Size.smul ..).trans_le (mul_le_mul_of_nonneg_left (hf i).2.1 (norm_nonneg (g i))))).trans ht)
  have hd:(Q.point P x).support=(U.point P x).support := by
    funext i; exact congr_fun (equalityS P Q U (code (Tally F) i).1) (code _ i).2
  exact Slate.density_difference (h.shines.represents N p j h.late.le).good
    (Q.prose P h hw hp hK x).2.1 (U.prose P h hw hp hK x).2.1 hR.conventional hd

lemma indexCost (hC : 0 ≤ C) :
    Costed (Q.index P h hw hp hK).toLinearMap (U.index P h hw hp hK).toLinearMap
      (stepAllowance F s ζ C) := fun x=>(profilePoint P h hc hw ha Q U hy hp hK hC x).2.1

local notation "f₁" => Q.recorded P h hw hl hp hK
local notation "f₂" => U.recorded P h hw hl hp hK
include hl
lemma recorder (hC : 0 ≤ C) (x:F.Coeff) :
    ‖f₁ x - f₂ x‖ ≤ stepAllowance F s ζ C * F.coeffSize x := by
  obtain ⟨hV,he,hR,-⟩:= profilePoint P h hc hw ha Q U hy hp hK hC x
  have hs:(Q.point P x).support=(U.point P x).support := by
    funext i; exact congr_fun (equalityS P Q U (code (Tally F) i).1) (code _ i).2
  apply (Coin.wealths _).mpr
  have hEq: Coin.uses (f₁ x - f₂ x) = capture (breakP (Q.point P x) (U.point P x)) P.down := by
    rw [map_sub]; exact (collected _ _ _ hs (Q.prose P h hw hp hK x).2.1 (U.prose P h hw hp hK x).2.1).symm
  rw [hEq]; exact alongPay hl _ _ hV hR.conventional

omit hc hw ha hy hp hl in
lemma manageable (hC : 0 ≤ C): stepAllowance F s ζ C * s ≤ C/4 := by
  have hs:s≥1:=(H.levels.params (j+1)).columns_ge
  have hF: ζ*s*orbitCost F ≤ barunit (H.S.block j) :=
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) h.budget.epsilon)
      (zero_le_one.trans (orbitCost_one_le F)))).trans h.budget.tiny
  unfold stepAllowance
  rw [show ζ*(C*s)*o*s=C*(ζ*s*o*s) from by ring]
  have h':= Gram.bank0 P h hK|>.2
  have hq:barunit (H.S.block j)*s ≤ 1/4 := by linarith only [h']
  exact (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hF (zero_le_one.trans hs)).trans hq) hC).trans_eq
    (by ring)

lemma withinStep (hC : 0 ≤ C): (Q.step P h hw hl hp hK).Within (U.step P h hw hl hp hK) (C/2) := by
  let B' := stepAllowance F s ζ C
  have hv':0 ≤ ζ:= h.budget.epsilon
  have hs:s≥1:=(H.levels.params (j+1)).columns_ge
  have hs':s'≥1:=(H.levels.params j).columns_ge
  apply Matric.Gram.ridge (zero_lt_one.trans_le hs) (zero_lt_one.trans_le hs') (Q.index P h hw hp hK)
    (U.index P h hw hp hK) f₁ f₂ _ _ (fun i=>(Q.prose P h hw hp hK i).2.2) (fun _=>signs ..) (fun _=>signs ..)
    (indexCost P h hc hw ha Q U hy hp hK hC) (recorder P h hc hw ha Q U hy hp hK hl hC) ?_ (div_nonneg hC zero_le_two) ?_
  · exact mul_nonneg (mul_nonneg hv' (mul_nonneg hC (zero_le_one.trans hs))) (zero_le_one.trans (orbitCost_one_le F))
  rw [mul_assoc]; refine (mul_le_mul (show 1+s' ≤ 2*s' by linarith only [hs'])
    (manageable P h hK hC) (by -- expose resident
      have ht:0 ≤ B' := mul_nonneg (mul_nonneg hv' (mul_nonneg hC (zero_le_one.trans hs)))
        (zero_le_one.trans (orbitCost_one_le F)); exact mul_nonneg ht (zero_le_one.trans hs))
      (by linarith only [hs'])).trans_eq ?_
  ring

end YM.Pier
