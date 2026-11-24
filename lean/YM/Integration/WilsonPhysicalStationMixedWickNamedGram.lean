import YM.Integration.WilsonPhysicalStationMixedWickNamedPrice
import YM.Integration.WilsonPhysicalStationMixedWickRespondents
import YM.Integration.WilsonPhysicalStationMixedWickPivots
import YM.Integration.WilsonPhysicalStationMixedNamedProbe
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerFrame

/-! The weighted paycheck for each entry of the physical lower Gram uses
the entire pre-reflected name and the entire original neutral respondent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickNamedGram
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀m,Vane R.family m){m D:ℕ}(B:Deck G)(e:ℕ)(a:Axis)
    (K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
set_option quotPrecheck false
local notation "C₀" => Cells.standard R.family
local notation "AX" => R.family.path.levels
local notation "I" => Glyph B e
local notation "T₀" => (AX).clock.monitor (V m).k

def electrode (b:(R.family.labels.level e).Index):Slot R.family:=⟨e,e,b,1,0,K,compact,clear⟩

def amount (i j:I):ℝ:=∑b,‖coefficient R B e j b‖*
  WilsonPhysicalStationMixedWickNamedPrice.price R (electrode R e K compact clear b) (reflected R B a i)

theorem target (y:Points 2)(i j:I):
    reference R.family (ladder R.family e (reflected R B a i)) (named R B e j) y=panel R B e a y i j:=by
  unfold WilsonPhysicalStationMixedWickTest.reference WilsonPhysicalStationMixedWickTest.fields
  rw [Further.CorrectedLift.ladder_reads]
  rfl

include F in
theorem original (he:e < m+1)(checked:(V m).checked f H m){M c:ℝ}
    (filed:Filed (f:=f) (l:=ℓ) J₀ J V e m M c)(simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    (sales:∀b,Sold R (V m) (electrode R e K compact clear b) he he D checked)
    (ξ:Points 2)(member:tested AX (V m).b (V m).k ξ∈K)(fits:FitSky AX (V m).b (V m).k ξ)(i j:I):
    ((D:ℝ)+1)*(T₀)^((j.2.1.val-i.2.1.val:ℕ):ℝ)*
      ‖frame R (J.U m) B e a ((V m).wheel.r • tested AX (V m).b (V m).k ξ) i j-
        panel R B e a (tested AX (V m).b (V m).k ξ) i j‖≤amount R B e a K compact clear i j:=by
  let y:=tested AX (V m).b (V m).k ξ
  let w:=WilsonPhysicalStationMixedWickPivots.reflected R B a i
  let survey:=electrode R e K compact clear
  let factor:ℝ:=((D:ℝ)+1)*(T₀)^((j.2.1.val-i.2.1.val:ℕ):ℝ)
  rw [←target]
  change factor*‖WilsonPhysicalStationLowerReceiver.ear R (S:=S) ((V m).wheel.r • y)
    ((J.U m e) (named R B e j)) ((J.U m e) w)-reference R.family (ladder R.family e w) (named R B e j) y‖≤_
  rw [←WilsonPhysicalStationMixedWickRespondents.incurred]
  apply WilsonPhysicalStationMixedWickRespondents.priced R (J.U m) _ _ w (named R B e j)
    (fun b=>probe R.family b 1 0) (coefficient R B e j)
    (WilsonPhysicalStationMixedNamedProbe.original R B e j) factor (mul_nonneg (by positivity) (Real.rpow_nonneg (Real.exp_pos _).le _))
  intro b live
  have rightGrade:rank R.family e b=j.2.1.val:=congrArg Prod.snd (WilsonPhysicalStationMixedNamedProbe.grades R B e j b live)
  have heard:=WilsonPhysicalStationMixedWickNamedPrice.original R F J₀ J V (survey b) he he checked
    filed filed simple below (sales b) w i.2.1.val (WilsonPhysicalStationMixedWickPivots.original R B a i)
    ξ member fits
  rw [WilsonPhysicalStationMixedWickRespondents.incurred,WilsonPhysicalStationLowerReceiver.evaluated]
  change ((D:ℝ)+1)*(T₀)^((rank R.family e b-i.2.1.val:ℕ):ℝ)*_≤_ at heard
  rw [rightGrade] at heard
  exact heard

end YM.Integration.WilsonPhysicalStationMixedWickNamedGram
end
