import YM.Integration.WilsonEmittedWindingBalance
import YM.Integration.WilsonEmittedFiledValues
import YM.Integration.WilsonOriginalFullRosterNativeCrop
import YM.Integration.WilsonOriginalFiledGroupReturn

/-! Evaluation of the complete, unmasked planted group functions at the original field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterGroupReturn
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ν ℓ : A→ℕ)
variable (B : BudgetPoint) {σ b K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
variable (s : Multi.Hot Γ) (v : V) (hv : v∈s.val.val)
variable (tube : LinkTube G) {m j l J : ℕ} {W ε : ℝ}
local notation "q" a:max => (fun i:I a=>(M a i).paint (x a))
local notation "sum" => words M x c ℓ
local notation "near" => (fun a=>early (M a) s.val m)
local notation "far" => (fun a=>late (M a) s.val m)
local notation "total" => (fun a=>picked (M a) s.val)
local notation "full" => (fun z:Chart G n=>sum total z.1 (increment 1 z.2))
local notation "fee" u:max => rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
  (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s.val J u
local notation "paid" a:max => staff M w grades x B old scope a

local notation "hardCap" => WilsonEmittedLongInvoice.gross w c ν B s.val m g p pieces depth b θ


include scope old hv in
theorem original {H:Type} [Fintype H] (site:H→Site n)(owner:A→H)
    (fronts:∀a,(P a).origin v=site (owner a))
    {q₀:ℕ}(closed:∀a,q₀+ν a=ℓ a+(Launch.index Γ (grades a) s.val+1))
    (hε:0 ≤ ε)(read:∀i<j,∑u:Fin i→WilsonEmittedRootedJetWage.Slot G n,
      ‖iteratedFDeriv ℝ i full 0 (WilsonEmittedRootedJetWage.peg G n ∘ u)‖ ≤ ε)
    (positive:0<g)(small:g ≤ 1)(hj:j ≤ J)(hl:l ≤ j)
    (cutoff:m=WilsonOriginalSeparatedFrontClusters.crop B.B (Fintype.card H))
    (enrolled:64*(Fintype.card H+1) ≤ B.B)(room:Room B n tube B.B W)
    {C:A→ℝ}(wallet:∀a v,0<w a v)
    (gross:∀a,WilsonRootedKioskOccupiedSlip.Gross (rendered (M a) B g) (w a) B.B (B.supportExponent+2) (C a))
    (U:Config G n)(bright:∀u,Healthy B.threshold (neighborhood B.B (site u)) U):
    ‖∑a:A,c a • (g^(ν a) •
        (WilsonRootedKioskOccupiedSlip.bare (rendered (M a) B g) (x a) U).part s.val)‖ ≤
      (g^q₀)⁻¹*((l:ℝ)*(((j:ℝ)*ε+fee 0*g^(j-l))+fee m)+(fee 0)*W^l+g^q₀*hardCap):=by
  have widths:0 ≤ B.supportExponent+2:=by linarith only [B.exponent_pos]
  have raw (a:A):Summable (fun i=>Spill.raw (M a) g (x a) i U):=
    (WilsonRootedKioskCompleteFiling.sums (rendered (M a) B g) (wallet a) widths (gross a) (x a) U).1
  have printed:=WilsonEmittedFiledCatalogue.numerical M w grades x c ℓ B old scope s.val closed positive U raw
  change ‖∑a:A,c a • (g^(ν a) • (Spill.Foundry.uncut (M a) g (x a) U).part s.val)‖ ≤ _
  rw [←printed,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (pow_pos positive q₀))]
  exact mul_le_mul_of_nonneg_left (WilsonOriginalFullRosterNativeCrop.original M w grades x c ν ℓ B
    old scope s v hv tube site owner fronts closed hε read positive small hj hl cutoff enrolled room U bright)
    (inv_nonneg.mpr (pow_nonneg positive.le _))

end YM.Integration.WilsonOriginalFullRosterGroupReturn
end
