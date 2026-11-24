import YM.Integration.WilsonPhysicalStationMixedWickSolvent
import YM.Integration.WilsonPhysicalStationMixedWickCross

/-! A funded lower-coordinate invoice on the two actual original positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickLowerLaw
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace
open PhysMS Spec OPE Next.UVStress Trace.Pilot PhysicalNext.Repeat.Legato
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare Next.Rank.Station
open MS MS.Land MS.Menus MS.Theater XSpace.Structure1
open Local.Physical
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedBasisSale (Sold)
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonPhysicalStationMixedWickPivots (reflected)
open WilsonPhysicalStationMixedNamedProbe (coefficient)
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationMixedWickRespondents (balance)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel)
open WilsonPhysicalStationGradedLowerPanel (frame left right)
open Further.CorrectedLift (ladder)
open scoped BigOperators Classical Topology
open WilsonPhysicalStationGradedLowerPanel (cross)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickSolvent (Room)
open WilsonPhysicalStationGradedLowerPanel (charge)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)(V:∀m,Vane R.family m)(A:Slot R.family)
    {m D:ℕ}(hl:A.left < m+1)(hr:A.right < m+1)(B:Deck G)(a:Axis)
set_option quotPrecheck false
local notation "I" => Glyph B A.left
local notation "AX" => R.family.path.levels
local notation "T₀" => (AX).clock.monitor (V m).k
local notation "Q₀" => rank R.family A.right A.dual
local notation "z₀" => probe R.family A.dual A.turn A.arm


def ceiling (room:Room R (S:=S) B A.left a):ℝ:=
  room.cost*Classical.choose (WilsonPhysicalStationMixedWickCross.bounded R A B a)

include F in
theorem original (room:Room R (S:=S) B A.left a):
    0≤ceiling R A B a room ∧ ∀{Ml Bl Mr Br:ℝ}(checked:(V m).checked f H m)
    (_fileL:Filed (f:=f) (l:=ℓ) J₀ J V A.left m Ml Bl)
    (_fileR:Filed (f:=f) (l:=ℓ) J₀ J V A.right m Mr Br)(_simple:G.Simple)(_below:(ℓ:Filter _)≤f.fuse)
    (_sale:Sold R (V m) A hl hr D checked)
    (_gram:∀b,Sold R (V m) (WilsonPhysicalStationMixedWickNamedGram.electrode R A.left room.site room.compact room.clear b)
      hl hl D checked)(_hot:1≤T₀)(_late:room.floor≤D)
    (_inGram:tested AX (V m).b (V m).k room.ξ∈room.site)(_fitsGram:FitSky AX (V m).b (V m).k room.ξ)
    (ξ:Points 2)(_member:tested AX (V m).b (V m).k ξ∈A.site)(_fits:FitSky AX (V m).b (V m).k ξ)
    {h:ℕ}(le:A.left≤h)(_rpos:0<(V m).wheel.r),
    let xG:=(V m).wheel.r • tested AX (V m).b (V m).k room.ξ
    let x:=(V m).wheel.r • tested AX (V m).b (V m).k ξ
    let L:=(WilsonPhysicalStationLowerReceiver.ear R (e:=h) x ((J.U m A.right) z₀)).comp
      (F.sector.derivatives.rise le)
    IsUnit (WilsonPhysicalStationGradedLowerPanel.metered B A.left T₀ (frame R (J.U m) B A.left a xG)).det ∧
    (∑j:I,charge R (J.U m) B A.left a xG T₀ Q₀ L j • WilsonPhysicalStationLowerReceiver.ear R (e:=A.left)
      xG (WilsonPhysicalStationGradedLowerPanel.right R (J.U m) B A.left j)=L) ∧
    ∀j:I,‖charge R (J.U m) B A.left a xG T₀ Q₀ L j‖*T₀^Q₀ ≤ ceiling R A B a room*T₀^j.2.1.val:=by
  let roof:=Classical.choose (WilsonPhysicalStationMixedWickCross.bounded R A B a)
  obtain ⟨rp,cap⟩:=Classical.choose_spec (WilsonPhysicalStationMixedWickCross.bounded R A B a)
  refine ⟨mul_nonneg room.positive.le rp,?_⟩
  intro Ml Bl Mr Br checked fileL fileR simple below sale gram hot late inGram fitsGram ξ member fits h le rpos
  dsimp only
  let yG:=tested AX (V m).b (V m).k room.ξ
  let xG:=(V m).wheel.r • yG
  let y:=tested AX (V m).b (V m).k ξ
  let x:=(V m).wheel.r • y
  let L:=(WilsonPhysicalStationLowerReceiver.ear R (e:=h) x ((J.U m A.right) z₀)).comp (F.sector.derivatives.rise le)
  have near:=WilsonPhysicalStationMixedWickMetered.original R F J₀ J V B A.left a room.site
    room.compact room.clear checked hl Ml Bl fileL simple below hot gram room.ξ inGram fitsGram
  have measured:=room.solvent (J.U m) xG yG inGram T₀ (lt_of_lt_of_le zero_lt_one hot) D late near
  have priced:=measured.2 Q₀ L
  refine ⟨measured.1,priced.1,?_⟩
  have rates:=WilsonPhysicalStationMixedWickCross.original R F J₀ J V A hl hr B a checked
    fileL fileR simple below sale hot ξ member fits le rpos
  let row:=cross R (J.U m) B A.left a T₀ Q₀ L
  have cr:‖row‖≤roof:=by
    apply (pi_norm_le_iff_of_nonneg rp).mpr
    intro i
    let goal:=WilsonPhysicalStationMixedWickCross.base R A B a i y
    have actual:((D:ℝ)+1)*‖row i-goal‖≤WilsonPhysicalStationMixedWickCross.amount R A B a i:=rates i
    have err:‖row i-goal‖≤WilsonPhysicalStationMixedWickCross.amount R A B a i:=by
      have one:(1:ℝ)≤(D:ℝ)+1:=by linarith only [Nat.cast_nonneg (α:=ℝ) D]
      exact (le_mul_of_one_le_left (norm_nonneg _) one).trans actual
    have both:=norm_add_le (row i-goal) goal
    rw [sub_add_cancel] at both
    have maximum:‖goal‖+WilsonPhysicalStationMixedWickCross.amount R A B a i≤roof:=cap i y member
    linarith only [both,err,maximum]
  intro j
  have tpos:0≤T₀:=zero_le_one.trans hot
  calc
    _ ≤ T₀^j.2.1.val*room.cost*‖row‖:=priced.2 j
    _ ≤ T₀^j.2.1.val*room.cost*roof:=mul_le_mul_of_nonneg_left cr (mul_nonneg (pow_nonneg tpos _) room.positive.le)
    _ = _:=by change _=room.cost*roof*_; ring

end YM.Integration.WilsonPhysicalStationMixedWickLowerLaw
end
