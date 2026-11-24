import YM.Integration.WilsonMeasuredPublicEntranceWeakRaw
import YM.Integration.WilsonPhysicalStationMixedWickPair
import YM.Integration.WilsonPhysicalStationObservedGrid
import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins

/-! At the ordered regulator limit these are the two actual Scribe fields, at their own
possibly different heights, on the very same original reporter and placement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickMeasured
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Next.Rank Next.Rank.Station Next.Rank.Perch Next.Rank.Price
open Further.CorrectedLift (ladder)
open WilsonMovingForkReporterBothArms (Filed)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀m,Vane R.family m){m:ℕ}(dl dr:Fin (m+1))(checked:(V m).checked f H m)
local notation "AX" => R.family.path.levels
local notation "C₀" => Cells.standard R.family
local notation "A₀" => V m
local notation "ds" => grades dl dr

def joined (x:(C₀).Field dl)(z:(C₀).Field dr):(i:Fin 2)→S.Field (ds i):=
  Fin.cons (α:=fun i=>S.Field (ds i)) (J.U m dl x) (fun _=>J.U m dr z)

def watch (x:(C₀).Field dl)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  physical (C:=R.family) ds j o p.1 p.2 (Fin.cons (α:=fun i=>R.family.label (ds i))
    ((A₀).wheel.atCut p dl x) (fun _=>(A₀).wheel.atCut p dr z))

variable {Ml Bl Mr Br:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V dl m Ml Bl)
    (right:Filed (f:=f) (l:=ℓ) J₀ J V dr m Mr Br)

include F left right checked in
theorem released (simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    (x:(C₀).Field dl)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (watch R V dl dr x z j o) (ℓ:Filter _) (𝓝 (S.classMoment S ds (Extraction.Order.grid R.family j o)
      (joined R J (m:=m) dl dr x z))):=by
  obtain ⟨X,hx,_,_⟩:=WilsonMeasuredPublicEntranceWeakRaw.original (R:=R) (Nat.le_of_lt_succ dl.isLt) checked left x
  obtain ⟨Y,hy,_,_⟩:=WilsonMeasuredPublicEntranceWeakRaw.original (R:=R) (Nat.le_of_lt_succ dr.isLt) checked right z
  let v(p:ℕ×ℕ):R.family.book.Vector ds:=Fin.cons (α:=fun i=>R.family.label (ds i)) (X.source p) (fun _=>Y.source p)
  let t:R.family.book.Vector ds:=Fin.cons (α:=fun i=>R.family.label (ds i)) X.label (fun _=>Y.label)
  have flow(i:Fin 2):Tendsto (fun p=>v p i) (ℓ:Filter _) (𝓝 (t i)):=by
    fin_cases i
    · exact X.approaches
    · exact Y.approaches
  have agrees:(fun i:Fin 2=>S.project (ds i) (t i))=joined R J (m:=m) dl dr x z:=by
    funext i
    fin_cases i
    · exact X.represents
    · exact Y.represents
  have same(p:ℕ×ℕ):watch R V dl dr x z j o p=physical (C:=R.family) ds j o p.1 p.2 (v p):=by
    simp only [watch,v,hx,hy]
  have projected:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) ds safe t
  rw [←agrees,projected]
  exact (WilsonMeasuredPublicEntranceSeparatedPins.variation R F ds j o simple below v t flow safe).congr' (Eventually.of_forall fun p=>(same p).symm)

theorem printed {p:ℕ×ℕ}(fine:(A₀).k<p.1)(x:(C₀).Field dl)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover):
    watch R V dl dr x z j o p=cell R (A₀) dl dr (N:=p.1) (p:=p.2) checked fine j o (ladder R.family dl x) z:=by
  unfold cell
  simp only [WilsonPhysicalStationMixedWickPair.offered,WilsonPhysicalStationThermalPair.lifted]
  rfl

include F left right in
theorem original (simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)(x:(C₀).Field dl)(z:(C₀).Field dr)
    (ξ:Points 2)(fits:FitSky AX (A₀).b (A₀).k ξ)(scale fee:ℝ)
    (cash:∀ᶠ N:ℕ in atTop,∀p:ℕ,∀fine:(A₀).k<N,
      scale*‖cell R (A₀) dl dr (p:=p) checked fine (A₀).k (choose AX (A₀).b (A₀).k ξ) (ladder R.family dl x) z-
        reference R.family (ladder R.family dl x) z (tested AX (A₀).b (A₀).k ξ)‖ ≤ fee):
    scale*‖S.classMoment S ds ((A₀).wheel.r • tested AX (A₀).b (A₀).k ξ) (joined R J (m:=m) dl dr x z)-
      reference R.family (ladder R.family dl x) z (tested AX (A₀).b (A₀).k ξ)‖ ≤ fee:=by
  let o:=choose AX (A₀).b (A₀).k ξ
  have flow:=released R F J₀ J V dl dr checked left right simple below x z (A₀).k o
    (WilsonPhysicalStationObservedGrid.separated R (A₀) ξ fits)
  rw [WilsonPhysicalStationObservedGrid.actual R (A₀) ξ] at flow
  apply le_of_tendsto (tendsto_const_nhds.mul ((flow.sub tendsto_const_nhds).norm))
  obtain ⟨N₀,lo⟩:=eventually_atTop.mp cash
  filter_upwards [WilsonPhysicalStationElectedEars.ready (f:=f) (ℓ:=ℓ) below N₀,
    WilsonPhysicalStationElectedEars.ready (f:=f) (ℓ:=ℓ) below (A₀).k] with p age fine
  rw [printed R V dl dr checked fine]
  exact lo p.1 age.le p.2 fine

end YM.Integration.WilsonPhysicalStationMixedWickMeasured
end
