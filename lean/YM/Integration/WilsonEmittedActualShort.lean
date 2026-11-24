import YM.Integration.WilsonEmittedOutputPower
import YM.Integration.WilsonEmittedCompactBalance

/-! The full cutoff-uniform short regular comparison of the original deposited and prescribed catalogues. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedActualShort
open Finset Function Wilson RG Lattice QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Marker AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Comparison.Density.Transport RG.Supply WilsonEmittedWordJointFare WilsonEmittedFiledCatalogue
open WilsonEmittedDictionary WilsonEmittedStageFinance WilsonEmittedJoinedFares
open WilsonEmittedCutGrouping
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius

private theorem strip {B:BudgetPoint} {K a g σ θ H:ℝ} (paid:Invoice.Supports B K a g σ θ)
    (sized:B.B=Nat.ceil ((Real.log H)^2)) (reserve:Real.exp ((σ⁻¹)^2)≤H)
    (cap:a≤102) (T:ℕ) (late:(256*((T:ℝ)+1))^2≤Real.log H) :
    Invoice.Supports B K a g σ (WilsonEmittedCompactTariff.strip σ) ∧
    Real.exp (-WilsonEmittedCompactTariff.strip σ)^(B.B/32)≤(H^T)⁻¹ := by
  obtain ⟨wide,_⟩:=WilsonEmittedLengthWindow.decays paid sized reserve cap T late
  obtain ⟨hg,h1,hK,ht,hσ,ha,hθ,hr⟩:=wide
  have hs:0<σ:=by linarith [mul_nonneg ha (inv_nonneg.mpr (Nat.cast_nonneg B.B))]
  have bought:Invoice.Supports B K a g σ (WilsonEmittedCompactTariff.strip σ):=by
    refine ⟨hg,h1,hK,ht,hσ,ha,lt_min zero_lt_one (by positivity),?_⟩
    have brief:WilsonEmittedCompactTariff.strip σ≤WilsonEmittedLengthWindow.strip θ σ:=le_max_right .. 
    linarith
  refine ⟨bought,?_⟩
  have ready:=(WilsonEmittedLengthWindow.decays bought sized reserve cap T late).2
  simpa only [WilsonEmittedLengthWindow.strip,WilsonEmittedCompactTariff.strip,max_self] using ready

variable {G:Gauge} {n:Side} {A V:Type} [Fintype A] [DecidableEq V] {Γ:Census V}
variable {I X:A→Type} {P:A→Passport n V}
variable (M:(a:A)→I a→Row (P a) Γ G (X a)) (w:A→V→ℝ) (grades:A→V→ℕ)
variable (x:(a:A)→X a) (c:A→ℝ) (ℓ:A→ℕ) (p pieces depth:A→ℕ) (b α σ:A→ℝ)
variable {K θ:A→ℝ} (B:BudgetPoint) {g:ℝ}
variable (old:∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope:∀a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s:Multi.Hot Γ) (v:V) (hv:v∈s.val.val) (L:A→Layout G) (tape:A→Finset Age)
variable (tube:LinkTube G) (Z:Patch) (kern:KernelChoices) (O:Stage)
local notation "t₀"=>B.B/32
local notation "near"=>fun a=>early (M a) s.val t₀
local notation "r" j:max m:max =>rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
    (b:=b) (α:=α) (θ:=fun a=>WilsonEmittedCompactTariff.strip (σ a)) s.val j m

include old scope hv in
theorem original (T k:ℕ) {y:Site n} {W H β:ℝ} (money:0<g) (g1:g≤1)
    (hp:0<H) (bb:0<β) (upper:β≤2*H) (coin:g=(Real.sqrt β)⁻¹)
    (ord:B.order=O.order) (power:B.power=O.power) (sized:B.B=Nat.ceil ((Real.log H)^2))
    (late:(256*((T:ℝ)+1))^2≤Real.log H) (hg:0≤Real.log H)
    (reserve:∀a,0≤b a ∧ α a≤102 ∧ 0<σ a ∧ Real.exp (((σ a)⁻¹)^2)≤H)
    (school:∀a,p a+depth a+1≤capacity Z k ∧ pieces a≤capacity Z k ∧ ℓ a≤capacity Z k)
    (tab:(program tube Z kern O k)^3*(1+Real.log H)^(orderBill Z O k)≤g⁻¹)
    (held:W≤2*g^(1/2:ℝ)) (W0:0≤W) (room:Room B n tube (B.B+1) W)
    (grade:3*T≤k) (home:∀a,(P a).origin v=y)
    (read:∀i<3*T,∀u:Directions G n,(∑a:A,c a • WilsonEmittedFiledGerm.price M grades x ℓ s L tape i u a)=0) :
    B.Regular (neighborhood (B.B+1) y) (words M x c ℓ near g) ∧
    B.supBounds y (neighborhood (B.B+1) y) (words M x c ℓ near g)
      (WilsonEmittedOutputPower.constant T * (cash s.val w c b*g⁻¹) * g^T) := by
  have both a:=strip (scope a) sized (reserve a).2.2.2 (reserve a).2.1 T late
  let J:=max B.order k
  have cap:3*T≤J:=grade.trans (le_max_right ..)
  have within:2*t₀≤B.B:=by omega
  have good:=WilsonEmittedCompactBalance.original M w grades x c ℓ B old
    (fun a=>(both a).1) s v hv L tape tube read home money g1 cap (show 2*T≤3*T by omega)
    (le_max_left ..) (show separation y y≤0 by simp) le_rfl (show 2*t₀ < B.B+1 by omega) room
  have toll a:0<Poly.toll (w a) s.val:=Poly.worth (old a).positive s.val
  have low:=WilsonEmittedRootedFinance.posted tube Z kern O B s.val w c ℓ p pieces depth b α σ
    k (2*t₀) 0 ord power hg sized within zero_le_one tab school toll reserve (by simp)
  have high:=WilsonEmittedRootedFinance.posted tube Z kern O B s.val w c ℓ p pieces depth b α σ
    k (2*t₀) t₀ ord power hg sized within (inv_nonneg.mpr (pow_nonneg hp.le _)) tab school toll
    reserve (fun a=>(both a).2)
  rw [mul_one] at low
  have A0:0≤cash s.val w c b*g⁻¹:=mul_nonneg (sum_nonneg fun a _=>
    mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr (toll a).le) (reserve a).1)) (inv_nonneg.mpr money.le)
  have val:=WilsonEmittedOutputPower.retained T money W0 (price_nonneg tube B.order) A0 low high held
    (WilsonEmittedOutputPower.tail hp bb upper g coin g1 T)
  refine ⟨good.1,good.2.1.trans val,?_⟩
  intro U passes faces tested bounds
  exact (good.2.2 U passes faces tested bounds).trans val

end YM.Integration.WilsonEmittedActualShort
end
