import YM.Integration.WilsonPhysicalStationMixedWickNamedGram
import YM.Integration.WilsonPhysicalStationMixedWickForeignPanel
import YM.Integration.WilsonPhysicalStationMixedWickCurrency

/-! The original right high peer on the genuine lower-height Gram electrodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickCross
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
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)(V:∀m,Vane R.family m)(A:Slot R.family)
    {m D:ℕ}(hl:A.left < m+1)(hr:A.right < m+1)(B:Deck G)(a:Axis)
set_option quotPrecheck false
local notation "I" => Glyph B A.left
local notation "AX" => R.family.path.levels
local notation "T₀" => (AX).clock.monitor (V m).k
local notation "Q₀" => rank R.family A.right A.dual
local notation "z₀" => probe R.family A.dual A.turn A.arm

def base (i:I)(y:Points 2):ℂ:=reference R.family
  (ladder R.family A.left (WilsonPhysicalStationMixedWickPivots.reflected R B a i)) z₀ y
def amount (i:I):ℝ:=WilsonPhysicalStationMixedWickNamedPrice.price R A
  (WilsonPhysicalStationMixedWickPivots.reflected R B a i)

theorem bounded :∃C:ℝ,0≤C ∧ ∀i:I,∀y∈A.site,‖base R A B a i y‖+amount R A B a i≤C:=by
  have smooth (i:I):ContinuousOn (base R A B a i) (conf 2):=by
    let w:=WilsonPhysicalStationMixedWickPivots.reflected R B a i
    let v:=WilsonPhysicalStationMixedWickTest.fields R.family (ladder R.family A.left w) z₀
    exact ((Bel R.family.book).class_smooth (Bel R.family.book) (Maxwell.table_smooth R.family.labels)
      (fun k=>⟨grades A.left A.right k,v k⟩)).continuousOn
  choose bounds paid using fun i:I=>A.compact.exists_bound_of_continuousOn ((smooth i).mono A.clear)
  let K:=fun i:I=>|bounds i|+|amount R A B a i|
  refine ⟨∑i:I,K i,Finset.sum_nonneg (fun i _=>add_nonneg (abs_nonneg _) (abs_nonneg _)),?_⟩
  exact fun i y hy=>(add_le_add ((paid i y hy).trans (le_abs_self _)) (le_abs_self _)).trans
    (Finset.single_le_sum (f:=K) (fun j _=>add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i))

include F in
theorem original {Ml Bl Mr Br:ℝ}(checked:(V m).checked f H m)
    (fileL:Filed (f:=f) (l:=ℓ) J₀ J V A.left m Ml Bl)
    (fileR:Filed (f:=f) (l:=ℓ) J₀ J V A.right m Mr Br)(simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse)
    (sale:Sold R (V m) A hl hr D checked)(hot:1≤T₀)
    (ξ:Points 2)(member:tested AX (V m).b (V m).k ξ∈A.site)(fits:FitSky AX (V m).b (V m).k ξ)
    {h:ℕ}(le:A.left≤h)(rpos:0<(V m).wheel.r):
    let x:=(V m).wheel.r • tested AX (V m).b (V m).k ξ
    let Z:=(J.U m A.right) z₀
    let L:=(WilsonPhysicalStationLowerReceiver.ear R (e:=h) x Z).comp (F.sector.derivatives.rise le)
    ∀i:I,((D:ℝ)+1)*‖cross R (J.U m) B A.left a T₀ Q₀ L i-base R A B a i (tested AX (V m).b (V m).k ξ)‖
      ≤amount R A B a i:=by
  dsimp only
  let y:=tested AX (V m).b (V m).k ξ
  let x:=(V m).wheel.r • y
  let z:=(J.U m A.right) z₀
  have fit:x∈conf 2:=Work.A05.smul_conf rpos (A.clear member)
  rw [WilsonPhysicalStationLowerReceiver.raised R F le x fit z]
  intro i
  let w:=WilsonPhysicalStationMixedWickPivots.reflected R B a i
  let val:=WilsonPhysicalStationLowerReceiver.ear R x z ((J.U m A.left) w)
  let goal:=base R A B a i y
  have received:=WilsonPhysicalStationMixedWickNamedPrice.original R F J₀ J V A hl hr checked
    fileL fileR simple below sale w i.2.1.val (WilsonPhysicalStationMixedWickPivots.original R B a i)
    ξ member fits
  have realFee:((D:ℝ)+1)*(T₀)^((Q₀-i.2.1.val:ℕ):ℝ)*‖val-goal‖≤amount R A B a i:=by
    dsimp only [val]
    rw [WilsonPhysicalStationLowerReceiver.evaluated]
    exact received
  have foreign (diff:i.2.1.val≠Q₀):goal=0:=
    WilsonPhysicalStationMixedWickForeignPanel.ballot R _ i.2.1.val
      (WilsonPhysicalStationMixedWickPivots.original R B a i) A.dual A.turn A.arm y diff
  have paid:=WilsonPhysicalStationMixedWickCurrency.restored hot (by positivity : 0≤(D:ℝ)+1)
    Q₀ i.2.1.val val goal foreign realFee
  change ((D:ℝ)+1)*‖(T₀:ℂ)^Q₀/(T₀:ℂ)^i.2.1.val*val-goal‖≤_
  rwa [mul_comm ((T₀:ℂ)^Q₀/(T₀:ℂ)^i.2.1.val)]

end YM.Integration.WilsonPhysicalStationMixedWickCross
end
