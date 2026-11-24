import YM.Integration.WilsonOriginalFullRosterGroupReturn
import YM.Integration.WilsonOriginalCensusAngularFace

/-! The actual signed angular account pays the difference of the original two unmasked posts
on the common short field, with the genuine group and derivative tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterAngularReturn
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonOriginalCensusAngularFace WilsonEmittedFiledCatalogue
open AnalyticBridge.SectorAffine.Offset
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
private abbrev sign (a:Bool):ℝ:=if a then -1 else 1
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{Γ:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}(M:(a:Bool)→I a→Row (P a) Γ G (X a))
  (w:Bool→V→ℝ)(grades:Bool→V→ℕ)(x:(a:Bool)→X a)
  (B:BudgetPoint)(σ b θ:Bool→ℝ)(p pieces depth:Bool→ℕ)(g:ℝ)
  (s:Multi.Hot Γ)(v:V)(o:Site n)(tube:LinkTube G)

def price (G:Gauge){V:Type}[DecidableEq V]{Γ:Census V}(s:Multi.Hot Γ)
    (w:Bool→V→ℝ)(ℓ p pieces depth:Bool→ℕ)(b θ:Bool→ℝ)(B:BudgetPoint)
    (g width ε:ℝ)(pole T J fronts:ℕ):ℝ:=
  let m:=WilsonOriginalSeparatedFrontClusters.crop B.B fronts
  let fee:=fun u=>rent (G:=G) w sign ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
    (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s.val J u
  (g^pole)⁻¹*((2*T:ℕ)*(((3*T:ℕ):ℝ)*ε+fee 0*g^(3*T-2*T)+fee m)+fee 0*width^(2*T)+
    g^pole*WilsonEmittedLongInvoice.gross w sign (fun _=>0) B s.val m g p pieces depth b θ)

theorem original {K:Bool→ℝ}
    (old:∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
    (scope:∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
    (hv:v∈s.val.val){δ:ℝ}(q:Probe M w grades x B σ b θ p pieces depth g s v o tube δ)
    {H:Type}[Fintype H](site:H→Site n)(owner:Bool→H)(fronts:∀a,(P a).origin v=site (owner a))
    (enrolled:64*(Fintype.card H+1) ≤ B.B)(U:Config G n)
    (bright:∀u,Healthy B.threshold (neighborhood B.B (site u)) U):
    ‖(WilsonRootedKioskOccupiedSlip.bare (rendered (M false) B g) (x false) U).part s.val-
      (WilsonRootedKioskOccupiedSlip.bare (rendered (M true) B g) (x true) U).part s.val‖ ≤
      price G s w q.ℓ p pieces depth b θ B g q.width q.ε q.pole q.T q.J (Fintype.card H):=by
  let d (a:Bool):ℕ:=(∑u,grades a u)+1
  have indexed (a:Bool)(t:Γ.Mode):(∑u∈t.val,grades a u)+1 ≤ d a:=Nat.succ_le_succ
    (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades a) (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _))
  have gross a:=WilsonMarkedFixedPoleGross.landed (M a) (w a) (grades a) B (old a) (scope a) (d a) (indexed a)
  have read:=WilsonNeutralTwoPrintAccount.read M x grades old s ⟨v,hv⟩ q.layout q.tape q.legal q.ℓ B scope
    q.pole (3*q.T) (fun a=>(q.clearing a).symm) q.tolerance q.entries
  have bound:=WilsonOriginalFullRosterGroupReturn.original M w grades x sign (fun _=>0) q.ℓ B old scope
    s v hv tube site owner fronts q.clearing q.tolerance read (scope false).1 (q.small.trans (by norm_num))
    q.enough (show 2*q.T ≤ 3*q.T by omega) rfl enrolled q.room (fun a=>(old a).positive) gross U bright
  unfold price
  simpa [Fintype.sum_bool,sign,sub_eq_add_neg,add_comm] using bound

end YM.Integration.WilsonOriginalFullRosterAngularReturn
end
