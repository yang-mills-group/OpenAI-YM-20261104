import YM.Integration.WilsonEmittedStageFinance
import YM.Integration.WilsonEmittedShortTariff
import YM.Integration.WilsonEmittedJoinedFares

/-! A single paid real strip controls the complete derivative of the signed short roster on the actual receiving stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedRootedFinance
open Marker Wilson RG Lattice RG.Supply QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonEmittedDictionary WilsonEmittedStageFinance WilsonEmittedJoinedFares
variable {G:Gauge} (tube:LinkTube G) (X:Patch) (K:KernelChoices) (O:Stage) (B:BudgetPoint)
variable {V A:Type} [Fintype A] [DecidableEq V] {Γ:Census V}
variable (s:Γ.Mode) (w:A→V→ℝ) (c:A→ℝ) (shift p pieces depth:A→ℕ) (b α σ:A→ℝ)

local notation "r" j:max m:max =>
  WilsonEmittedFiledCatalogue.rent (G:=G) w c shift B (p:=p) (pieces:=pieces) (depth:=depth)
    (b:=b) (α:=α) (θ:=fun u=>WilsonEmittedCompactTariff.strip (σ u)) s j m

theorem posted (k a m:ℕ) {H Ω τ:ℝ}
    (ord:B.order=O.order) (pow:B.power=O.power)
    (hg:0≤Real.log H) (square:B.B=Nat.ceil ((Real.log H)^2)) (within:a≤B.B) (ht:0≤τ)
    (funded:(program tube X K O k)^3*(1+Real.log H)^(orderBill X O k)≤Ω)
    (school:∀u,p u+depth u+1≤capacity X k ∧ pieces u≤capacity X k ∧ shift u≤capacity X k)
    (price:∀u,0<Poly.toll (w u) s) (old:∀u,0≤b u ∧ α u≤102 ∧ 0<σ u ∧ Real.exp (((σ u)⁻¹)^2)≤H)
    (tail:∀u, Real.exp (-WilsonEmittedCompactTariff.strip (σ u))^m≤τ) :
    Anchor.focus a 0 B^B.order * |groupPrice tube B.order| *(r (max B.order k) m) ≤
      cash s w c b * Ω * τ := by
  let J:=max B.order k
  let C:=program tube X K O k
  let z:=1+Real.log H
  let E:=2*B.power*B.order
  have jj:J=max O.order k:=by dsimp [J];rw [ord]
  have parts:=WilsonEmittedStageFinance.parts tube X K O k
  have hC:0≤C:=zero_le_one.trans parts.1
  have hG:0≤|groupPrice tube B.order|:=abs_nonneg _
  have hw:0≤cash s w c b:=Finset.sum_nonneg (fun u _=>mul_nonneg (abs_nonneg _)
    (mul_nonneg (inv_nonneg.mpr (price u).le) (old u).1))
  have zpos:1≤z:=by dsimp [z];linarith
  have fpos:0≤Anchor.focus a 0 B^B.order:=by unfold Anchor.focus;positivity
  have hz E:0≤z^E:=pow_nonneg (zero_le_one.trans zpos) (E:ℕ)
  have aC:Anchor.focus a 0 B^B.order≤C*z^E:=
    (WilsonEmittedShortTariff.focus B hg square within).trans
      (mul_le_mul_of_nonneg_right (by rw [pow,ord];exact parts.2.2.1) (hz _))
  have gC:|groupPrice tube B.order|≤C:=by rw [ord];exact parts.2.1
  have fr:Anchor.focus a 0 B^B.order*|groupPrice tube B.order|≤(C*z^E)*C:=
    mul_le_mul aC gC hG (mul_nonneg hC (hz E))
  have age (u:A):|WilsonEmittedTransitionJet.fee J (shift u)
      (WilsonEmittedCompactTariff.fixed G J (p u+depth u+1) (pieces u))|≤C:=by
    rw [jj];exact school_word tube O X K (school u).1 (school u).2.1 (school u).2.2
  have rent:=WilsonEmittedJoinedFares.original G B s w c shift p pieces depth b α σ zpos ht square age
    (fun u=>(school u).1) price old tail
  have upper:0≤cash s w c b*C*z^(13+J*capacity X k)*τ:=
    mul_nonneg (mul_nonneg (mul_nonneg hw hC) (hz _)) ht
  have compare:=(mul_le_mul_of_nonneg_left rent (mul_nonneg fpos hG)).trans
    (mul_le_mul_of_nonneg_right fr upper)
  apply compare.trans
  have ee: E+(13+J*capacity X k)=orderBill X O k:=by
    unfold E orderBill;rw [jj,pow,ord];omega
  calc
    (C*z^E*C)*(cash s w c b*C*z^(13+J*capacity X k)*τ) =
      cash s w c b*(C^3*(z^E*z^(13+J*capacity X k)))*τ:=by ring
    _ = cash s w c b*(C^3*z^(orderBill X O k))*τ:=by rw [←pow_add,ee]
    _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left funded hw) ht

end YM.Integration.WilsonEmittedRootedFinance
end
