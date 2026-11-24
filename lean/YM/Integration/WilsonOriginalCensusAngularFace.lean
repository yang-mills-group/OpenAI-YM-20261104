import YM.Integration.WilsonNeutralTwoPrintPrice
import YM.Integration.WilsonOriginalCensusRestamp

/-! The finite trace table used by one genuine held-field comparison. Every signed
coefficient is taken from the two submitted rosters, including the rank-zero entry. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusAngularFace
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset WilsonEmittedWordJointFare WilsonEmittedCutGrouping
open WilsonEmittedFiledCatalogue Push.AbsoluteSums WilsonRootedKioskOccupiedSlip
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius

universe u
def sides {Z:Sort u} (left right:Z) : Bool→Z | false=>left | true=>right
def roster {G:Gauge}{n:Side}{V I I' X X':Type}[DecidableEq V]{J:Census V}
    {left right:Passport n V}(L:I→Row left J G X)(R:I'→Row right J G X'):
    ∀a:Bool,sides I I' a→Row (sides left right a) J G (sides X X' a)
  | false=>L
  | true=>R
def tests {X X':Type} (x:X)(z:X'):∀a:Bool,sides X X' a | false=>x | true=>z

variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]{Γ:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}(M:(a:Bool)→I a→Row (P a) Γ G (X a))
  (w:Bool→V→ℝ) (grades:Bool→V→ℕ)(x:(a:Bool)→X a)
  (B:BudgetPoint)(σ b θ:Bool→ℝ)(p pieces depth:Bool→ℕ)(g:ℝ)
  (s:Multi.Hot Γ)(v:V)(o:Site n)(tube:LinkTube G)
private abbrev sign (a:Bool):ℝ:=if a then -1 else 1
local notation "jet" ℓ:max J:max => rent (G:=G) w sign ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
  (b:=b) (α:=fun _=>B.supportExponent+2) (θ:=θ) s.val J 0
local notation "word" => WilsonEmittedLongInvoice.gross w sign (fun _=>0) B s.val 0 g p pieces depth b θ

structure Probe (δ:ℝ) where
  pole : ℕ
  debit : ℕ
  target : ℕ
  T : ℕ
  chosen : T=pole+debit+target
  ℓ : Bool→ℕ
  clearing : ∀a,pole+0=ℓ a+(Launch.index Γ (grades a) s.val+1)
  layout : Bool→Layout G
  tape : Bool→Finset Age
  legal : ∀a,Legal (tape a) (layout a)
  ε : ℝ
  tolerance : 0 ≤ ε
  entries : ∀e,e+pole<3*T → ((e+pole).factorial:ℝ)*
    WilsonEmittedAngularJointFare.mass (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) (e+pole) ≤ ε
  home : ∀a,(P a).origin v=o
  small : g ≤ 1/2
  J : ℕ
  enough : 3*T ≤ J
  width : ℝ
  room : Room B n tube B.B width
  radius : 0 ≤ width
  held : width ≤ 2*g^(1/2:ℝ)
  hat : ℝ
  beta : ℝ
  hat_pos : 0<hat
  beta_pos : 0<beta
  thermal : beta ≤ 2*hat
  atDate : g=(Real.sqrt beta)⁻¹
  side : B.B=Nat.ceil ((Real.log hat)^2)
  tax : B.supportExponent+2 ≤ 102
  strip : ∀a,WilsonEmittedCompactTariff.strip (σ a) ≤ θ a
  reserve : ∀a,Real.exp ((σ a)⁻¹^2) ≤ hat
  onset : (256*((T:ℝ)+1))^2 ≤ Real.log hat
  C : ℝ
  cost_nn : 0 ≤ C
  jet_tariff : groupPrice tube 0*(jet ℓ J) ≤ C*(g^debit)⁻¹
  word_tariff : (word) ≤ C*(g^debit)⁻¹
  quote : ((g^pole)⁻¹*(groupPrice tube 0*((2*T:ℕ):ℝ)*((3*T:ℕ):ℝ)))*ε+
    (WilsonEmittedOutputPower.constant T+1)*C*g^target ≤ δ

theorem original {K:Bool→ℝ}(old:∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
    (scope:∀a,Invoice.Supports B (K a) (B.supportExponent+2) g (σ a) (θ a))
    (hv:v∈s.val.val){δ:ℝ}(q:Probe M w grades x B σ b θ p pieces depth g s v o tube δ):
    ∃r:WilsonOriginalOrdinaryFlatHulls.Row B tube o
      (fun U=>(bare (rendered (M false) B g) (x false) U).part s.val)
      (fun U=>(bare (rendered (M true) B g) (x true) U).part s.val),r.price ≤ δ:=by
  let d (a:Bool):ℕ:=(∑u,grades a u)+1
  have source (a:Bool)(t:Γ.Mode):(∑u∈t.val,grades a u)+1 ≤ d a:=Nat.succ_le_succ
    (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades a) (Finset.subset_univ _) (fun _ _ _=>Nat.zero_le _))
  have gross a:=WilsonMarkedFixedPoleGross.landed (M a) (w a) (grades a) B (old a) (scope a) (d a) (source a)
  obtain ⟨r,paid⟩:=WilsonNeutralTwoPrintPrice.original M w grades x q.ℓ B old scope s v hv tube
    q.pole q.debit q.target q.T q.chosen q.clearing q.layout q.tape q.legal q.tolerance q.entries q.home
    (scope false).1 q.small q.enough q.room q.radius q.held q.hat_pos q.beta_pos q.thermal q.atDate q.side q.tax
    q.strip q.reserve q.onset (fun a=>budget_nonneg ((old a).suggests 0)) (fun a=>(old a).positive)
    gross q.cost_nn q.jet_tariff q.word_tariff
  exact ⟨r,paid.trans q.quote⟩

end YM.Integration.WilsonOriginalCensusAngularFace
end
