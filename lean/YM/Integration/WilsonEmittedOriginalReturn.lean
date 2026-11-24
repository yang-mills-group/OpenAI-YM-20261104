import YM.Integration.WilsonEmittedActualShort
import YM.Integration.WilsonEmittedPostedFigure
/-! The regular and unrestricted group-field return at actual original measured dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedOriginalReturn
open Finset Filter Lattice Wilson RG RG.Supply Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Earn.Scene AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Comparison.Density.Transport Push.Local PhysicalNext PhysicalNext.Repeat.Legato
open WilsonLimitConstruction FundedDictionaryPatchPrices WilsonEmittedDictionary
open WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue WilsonEmittedJoinedFares
open WilsonEmittedSignedTariff
open scoped BigOperators Classical
variable {G:Gauge} (tube:LinkTube G) (R:Run G) (simple:G.Simple)
local notation "levels" => R.family.path.levels
local notation "budgetAt" j:max => (levels).budget (j+1)
local notation "hatAt" j:max => (levels).clock.hatBeta (j+1)
local notation "patchAt" j:max per:max => ((levels).clock.op j per).patch
local notation "betaAt" j:max N:max per:max => (R.family.path.rep N per (j+1)).beta
local notation "couplingAt" j:max N:max per:max => (Real.sqrt (betaAt j N per))⁻¹
local notation "sideAt" j:max per:max => (levels).S.side (j+1) per
local notation "chosenGrade" d:max q:max => 2*4+(d+1)+1+(q+3)

include simple in
theorem funded (bought:Covered (program tube) R) (strength:∀i,((levels).budget i).supportExponent ≤ 100)
    (d q k:ℕ) (clear:3*(chosenGrade d q) ≤ k) {δ:ℝ} (ep:0<δ) :
    ∀ᶠ j:ℕ in atTop,∀ (N per:ℕ), j+1 ≤ N →
    ∀ (A V:Type) [Fintype A] [DecidableEq V] (Γ:Census V)
      (I W:A→Type) (P:A→Passport (sideAt j per) V) (M:(a:A)→I a→Row (P a) Γ G (W a))
      (w:A→V→ℝ) (grades:A→V→ℕ) (x:(a:A)→W a) (c:A→ℝ)
      (ν ℓ p pieces depth height:A→ℕ) (b K σ:A→ℝ) (s:Multi.Hot Γ) (v:V)
      (L:A→Layout G) (tape:A→Finset Age) (y:Site (sideAt j per)) (mass:ℝ),
    let field:=words M x c ℓ (fun a=>early (M a) s.val ((budgetAt j).B/32)) (couplingAt j N per)
    let scale:=WilsonEmittedOutputPower.constant (chosenGrade d q) * (cash s.val w c b*(couplingAt j N per)⁻¹) * (couplingAt j N per)^(chosenGrade d q)
    let ζ:=fun a=>σ a/4
    let cube:=neighborhood ((budgetAt j).B+1) y
    let soft:=reservedMass (budgetAt j) cube (‖(↑(((couplingAt j N per)^(d+1))⁻¹):ℂ)‖*scale)+
      WilsonEmittedLongInvoice.budget (G:=G) w c ν (budgetAt j) s.val ((budgetAt j).B/32) (couplingAt j N per) p pieces depth K b ζ
    let raw:=fun m=>WilsonEmittedLongInvoice.gross w c ν (budgetAt j) s.val m (couplingAt j N per) p pieces depth b ζ
    (∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a)) →
    (∀a,Invoice.Supports (budgetAt j) (K a) ((budgetAt j).supportExponent+2) (couplingAt j N per) (σ a) (ζ a)) →
    (∀a,p a+depth a+1 ≤ capacity (patchAt j per) k ∧ pieces a ≤ capacity (patchAt j per) k ∧ ℓ a ≤ capacity (patchAt j per) k ∧
      height a ≤ capacity (patchAt j per) k ∧ depth a ≤ d) →
    (∀a,0 ≤ b a ∧ 0<σ a ∧ Real.exp (((σ a)⁻¹)^2) ≤ hatAt j) →
    (∀a, Real.exp ((ζ a)/2) ≤ 16*(2^(height a)*budgetR R (j+1)) ∧
      Invoice.price (budgetAt j) (K a) (p a+depth a+1) (pieces a) ((budgetAt j).supportExponent+2) (ζ a) G  ≤ 
          256*(2^(height a)*budgetR R (j+1))^3) →
    (v∈s.val.val) → (∀a,(P a).origin v=y) → 0 ≤ mass → cash s.val w c b ≤ 34*(hatAt j)^4*mass →
    (∀e<3*(chosenGrade d q),∀u:Directions G (sideAt j per),
      (∑a:A,c a • WilsonEmittedFiledGerm.price M grades x ℓ s L tape e u a)=0) →
    (budgetAt j).Regular cube field ∧ (budgetAt j).supBounds y cube field scale ∧ 0 ≤ scale ∧
      soft ≤ δ*(couplingAt j N per)^(q+2)*mass ∧ reservedMass (budgetAt j) cube (raw 0)+raw ((budgetAt j).B/32) ≤ hardCost d*(hatAt j)^(d+227)*mass :=by
  let T:=chosenGrade d q
  have calendar:=WilsonEmittedOriginalCalendar.funded tube R simple bought T k (cost:=softCost T q) ep
  filter_upwards [calendar] with j eligible N per live A V fin eq Γ I W P M w grades x c ν ℓ p pieces depth height b K σ s v L tape y mass
  dsimp only
  intro old scope school charged stamped selected home mass0 salary read
  let B:=(levels).budget (j+1)
  let X:=((levels).clock.op j per).patch
  let H:=(levels).clock.hatBeta (j+1)
  let m:=B.B/32
  let rm:=WilsonEmittedCubeRoom.width levels tube (j+1)
  let β:=(R.family.path.rep N per (j+1)).beta
  let g:=(Real.sqrt β)⁻¹
  have band: H/2 ≤ β ∧ β ≤ 2*H :=(R.makes.wilson.represents N per (j+1) live).band
  obtain ⟨H1,bb,gp,g1,small,logH,late,rpos,rbound,room,programPrice,capPrice,whole,budget⟩:=
    eligible per β band.1 band.2
  have strengthB:B.supportExponent+2 ≤ 102:=by have :=strength (j+1);change ((levels).budget (j+1)).supportExponent+2 ≤ 102;linarith
  have H0:0<H:=zero_lt_one.trans H1
  have Bsize:B.B=Nat.ceil ((Real.log H)^2):=rfl
  have opened a:=WilsonEmittedPostedFigure.school H0 (capacity X k) (p a+depth a+1) (pieces a) (height a)
    capPrice programPrice (school a).1 (school a).2.1 (school a).2.2.2.1
  have priced a:=WilsonEmittedPostedFigure.paid G B (p a) (depth a) (pieces a) (height a) T H0
    (zero_le_one.trans (QuadraticLocal.Advent.budget_pos (R:=R) (i:=j+1))) budget (opened a).2.2.2 strengthB Bsize late
    (charged a).2.2 (scope a) (stamped a).1 (stamped a).2
  have short:=WilsonEmittedActualShort.original M w grades x c ℓ p pieces depth b (fun _=>B.supportExponent+2)
    σ B old scope s v selected L tape tube X (levels).clock.kernel ((levels).params (j+1)) T k
    gp g1 H0 bb band.2 rfl rfl rfl Bsize late (zero_le_one.trans logH)
    (fun a=>⟨(charged a).1,strengthB,(charged a).2⟩)
    (fun a=>⟨(school a).1,(school a).2.1,(school a).2.2.1⟩) whole rbound rpos room clear home read
  have worth a:0<Poly.toll (w a) s.val:=Poly.worth (old a).positive s.val
  have value:=WilsonEmittedSignedTariff.onGroup (G:=G) B y s.val w c ν p pieces depth b K
    (fun a=>σ a/4) σ d (d+1) q T (by omega) rfl H1 bb band.1 band.2 rfl g1 logH Bsize strengthB mass0 worth salary
    (fun a=>⟨(opened a).1,(opened a).2.1,(opened a).2.2.1,(school a).2.2.2.2⟩)
    (fun a=>⟨(charged a).1,(charged a).2.1,(charged a).2.2,min_le_right ..,(priced a).1⟩)
    (fun a=>(priced a).2.1) (fun a=>(priced a).2.2)
  have bal:0 ≤ cash s.val w c b:=Finset.sum_nonneg (fun u _=>mul_nonneg (abs_nonneg _)
    (mul_nonneg (inv_nonneg.mpr (worth u).le) (charged u).1))
  have C0:0 ≤ WilsonEmittedOutputPower.constant T:=by unfold WilsonEmittedOutputPower.constant;positivity
  refine ⟨short.1,short.2,mul_nonneg (mul_nonneg C0 (mul_nonneg bal (inv_nonneg.mpr gp.le))) (pow_nonneg gp.le _),?_,value.2⟩
  exact value.1.trans (by
    calc
      softCost T q*mass*g^(q+3)=(softCost T q*g)*(g^(q+2)*mass):=by rw [show q+3=(q+2)+1 by omega,pow_succ];ring
      _  ≤  δ*(g^(q+2)*mass):=mul_le_mul_of_nonneg_right small (mul_nonneg (pow_nonneg gp.le _) mass0)
      _ = _:=by ring)

end YM.Integration.WilsonEmittedOriginalReturn
end
