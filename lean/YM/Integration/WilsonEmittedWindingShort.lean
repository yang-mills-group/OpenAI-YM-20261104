import YM.Integration.WilsonEmittedActualShort
import YM.Integration.WilsonEmittedWindingBalance
import YM.Integration.WilsonEmittedWindingFinance

/-! Price the actual short regular catalogue with its finite-period signed low jets. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedWindingShort
open Finset Function Wilson RG Lattice QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Marker AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Comparison.Density.Transport RG.Supply WilsonEmittedWordJointFare WilsonEmittedFiledCatalogue
open WilsonEmittedDictionary WilsonEmittedStageFinance WilsonEmittedJoinedFares
open WilsonEmittedCutGrouping
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G:Gauge} {n:Side} {A V:Type} [Fintype A] [DecidableEq V] {Γ:Census V}
variable {I X:A→Type} {P:A→Passport n V}
variable (M:(a:A)→I a→Row (P a) Γ G (X a)) (w:A→V→ℝ) (grades:A→V→ℕ)
variable (x:(a:A)→X a) (c:A→ℝ) (ℓ:A→ℕ) (p pieces depth:A→ℕ) (b α σ:A→ℝ)
variable {K:A→ℝ} (B:BudgetPoint) {g:ℝ}
variable (old:∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope:∀a,Invoice.Supports B (K a) (α a) g (σ a) (WilsonEmittedCompactTariff.strip (σ a)))
variable (s:Multi.Hot Γ) (v:V) (hv:v∈s.val.val)
variable (tube:LinkTube G) (Z:Patch) (kern:KernelChoices) (O:Stage)
local notation "t₀"=>B.B/32
local notation "near"=>fun a=>early (M a) s.val t₀
local notation "r" j:max m:max =>rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
    (b:=b) (α:=α) (θ:=fun a=>WilsonEmittedCompactTariff.strip (σ a)) s.val j m

include old scope hv in
theorem original (T k:ℕ) {y:Site n} {W H β δ:ℝ} (money:0<g) (g1:g≤1)
    (hp:0<H) (bb:0<β) (upper:β≤2*H) (coin:g=(Real.sqrt β)⁻¹)
    (ord:B.order=O.order) (power:B.power=O.power) (sized:B.B=Nat.ceil ((Real.log H)^2))
    (late:(256*((T:ℝ)+1))^2≤Real.log H) (hg:0≤Real.log H)
    (reserve:∀a,0≤b a ∧ α a≤102 ∧ 0<σ a ∧ Real.exp (((σ a)⁻¹)^2)≤H)
    (school:∀a,p a+depth a+1≤capacity Z k ∧ pieces a≤capacity Z k ∧ ℓ a≤capacity Z k)
    (tab:(program tube Z kern O k)^3*(1+Real.log H)^(orderBill Z O k)≤g⁻¹)
    (held:W≤2*g^(1/2:ℝ)) (W0:0≤W) (room:Room B n tube (B.B+1) W)
    (grade:3*T≤k) (home:∀a,(P a).origin v=y)
    (hδ:0 ≤ δ) (read:∀ i < 3*T,
      ∑ u:Fin i → WilsonEmittedRootedJetWage.Slot G n,
        ‖iteratedFDeriv ℝ i (fun z:WilsonEmittedWordJointFare.Chart G n =>
           words M x c ℓ (fun a=>picked (M a) s.val) z.1 (increment 1 z.2)) 0
          (WilsonEmittedRootedJetWage.peg G n ∘ u)‖ ≤ δ) :
    B.Regular (neighborhood (B.B+1) y) (words M x c ℓ near g) ∧
    B.supBounds y (neighborhood (B.B+1) y) (words M x c ℓ near g)
      (WilsonEmittedOutputPower.constant T * (cash s.val w c b*g⁻¹) * g^T+
        g⁻¹*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*δ) := by
  have tail a:Real.exp (-WilsonEmittedCompactTariff.strip (σ a))^t₀ ≤ (H^T)⁻¹:=by
    have line:=(WilsonEmittedLengthWindow.decays (scope a) sized (reserve a).2.2.2 (reserve a).2.1 T late).2
    simpa only [WilsonEmittedLengthWindow.strip,WilsonEmittedCompactTariff.strip,max_self] using line
  let J:=max B.order k
  have cap:3*T≤J:=grade.trans (le_max_right ..)
  have within:2*t₀≤B.B:=by omega
  have good:=WilsonEmittedWindingBalance.original M w grades x c ℓ B old scope s v hv tube hδ read home money g1 cap (show 2*T≤3*T by omega)
    (le_max_left ..) (show separation y y≤0 by simp) le_rfl (show 2*t₀ < B.B+1 by omega) room
  have toll a:0<Poly.toll (w a) s.val:=Poly.worth (old a).positive s.val
  have low:=WilsonEmittedRootedFinance.posted tube Z kern O B s.val w c ℓ p pieces depth b α σ
    k (2*t₀) 0 ord power hg sized within zero_le_one tab school toll reserve (by simp)
  have high:=WilsonEmittedRootedFinance.posted tube Z kern O B s.val w c ℓ p pieces depth b α σ
    k (2*t₀) t₀ ord power hg sized within (inv_nonneg.mpr (pow_nonneg hp.le _)) tab school toll
    reserve tail
  rw [mul_one] at low
  have A0:0≤cash s.val w c b*g⁻¹:=mul_nonneg (sum_nonneg fun a _=>
    mul_nonneg (abs_nonneg _) (mul_nonneg (inv_nonneg.mpr (toll a).le) (reserve a).1)) (inv_nonneg.mpr money.le)
  have val:=WilsonEmittedOutputPower.retained T money W0 (price_nonneg tube B.order) A0 low high held
    (WilsonEmittedOutputPower.tail hp bb upper g coin g1 T)
  have anchor:=WilsonEmittedWindingFinance.anchor tube Z kern O B k (2*t₀) ord power hg sized within tab
  have extra:Anchor.focus (2*t₀) 0 B^B.order*groupPrice tube B.order *
      (((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*δ) ≤ g⁻¹*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*δ:=by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right anchor (show 0≤((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)*δ by positivity)
  have all:=add_le_add val extra
  refine ⟨good.1,good.2.1.trans ?_,?_⟩
  · apply le_trans _ all
    simp only [show 3*T-2*T=T by omega,J]
    push_cast;ring_nf;exact le_rfl
  · intro U passes faces tested bounds
    apply (good.2.2 U passes faces tested bounds).trans
    apply le_trans _ all
    simp only [show 3*T-2*T=T by omega,J]
    push_cast;ring_nf;exact le_rfl

end YM.Integration.WilsonEmittedWindingShort
end
