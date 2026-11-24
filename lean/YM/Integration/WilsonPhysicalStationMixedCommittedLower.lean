import YM.Integration.WilsonPhysicalStationMixedWickMeasured

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedCommittedLower
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
open WilsonPhysicalStationSubtractedPair (lower)
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}(J₀:ℝ→tower S)(J:Scaling S)
    (V:∀m,Vane R.family m){m k:ℕ}(dl:Fin (k+1))(dr:Fin (m+1))(cb:(V k).checked f H k)(ca:(V m).checked f H m)
    {I:Type*}[Fintype I](c:I→ℂ)(w:I→(ℕ×ℕ)→R.family.label dl)(v:I→R.family.label dl)
local notation "AX" => R.family.path.levels
local notation "C₀" => Cells.standard R.family
local notation "A₀" => V m
local notation "ds" => grades dl dr

def joined (x:(C₀).Field dl)(z:(C₀).Field dr):(i:Fin 2)→S.Field (ds i):=
  Fin.cons (α:=fun i=>S.Field (ds i)) (J.U k dl x-S.project dl (∑i,c i • v i)) (fun _=>J.U m dr z)

def watch (x:(C₀).Field dl)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(p:ℕ×ℕ):ℂ:=
  physical (C:=R.family) ds j o p.1 p.2 (Fin.cons (α:=fun i=>R.family.label (ds i))
    ((V k).wheel.atCut p dl x-lower R c w p) (fun _=>(A₀).wheel.atCut p dr z))

variable {Ml Bl Mr Br:ℝ}(left:Filed (f:=f) (l:=ℓ) J₀ J V dl k Ml Bl)
    (right:Filed (f:=f) (l:=ℓ) J₀ J V dr m Mr Br)

include F left right cb ca in
theorem released (simple:G.Simple)(below:(ℓ:Filter _) ≤ f.fuse)
    (converges:∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory dl p.1 p.2).terminal (w i p)) (ℓ:Filter _) (𝓝 (v i)))
    (x:(C₀).Field dl)(z:(C₀).Field dr)(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (watch R V dl dr c w x z j o) (ℓ:Filter _) (𝓝 (S.classMoment S ds (Extraction.Order.grid R.family j o)
      (joined R J dl dr c v x z))):=by
  obtain ⟨X,hx,_,_⟩:=WilsonMeasuredPublicEntranceWeakRaw.original (R:=R) (Nat.le_of_lt_succ dl.isLt) cb left x
  obtain ⟨Y,hy,_,_⟩:=WilsonMeasuredPublicEntranceWeakRaw.original (R:=R) (Nat.le_of_lt_succ dr.isLt) ca right z
  let raw(p:ℕ×ℕ):R.family.book.Vector ds:=Fin.cons (α:=fun i=>R.family.label (ds i)) (X.source p-lower R c w p) (fun _=>Y.source p)
  let t:R.family.book.Vector ds:=Fin.cons (α:=fun i=>R.family.label (ds i)) (X.label-∑i,c i • v i) (fun _=>Y.label)
  have lo:Tendsto (lower R c w) (ℓ:Filter _) (𝓝 (∑i,c i • v i)):=
    tendsto_finsetSum _ (fun i _=>(converges i).const_smul (c i))
  have flow(i:Fin 2):Tendsto (fun p=>raw p i) (ℓ:Filter _) (𝓝 (t i)):=by
    fin_cases i
    · exact X.approaches.sub lo
    · exact Y.approaches
  have agrees:(fun i:Fin 2=>S.project (ds i) (t i))=joined R J dl dr c v x z:=by
    funext i
    fin_cases i
    · change S.project dl (X.label-∑i,c i • v i)=_
      rw [map_sub,X.represents]
      rfl
    · exact Y.represents
  have same(p:ℕ×ℕ):watch R V dl dr c w x z j o p=physical (C:=R.family) ds j o p.1 p.2 (raw p):=by
    simp only [watch,raw,hx,hy]
  have projected:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) ds safe t
  rw [←agrees,projected]
  exact (WilsonMeasuredPublicEntranceSeparatedPins.variation R F ds j o simple below raw t flow safe).congr' (Eventually.of_forall fun p=>(same p).symm)


end YM.Integration.WilsonPhysicalStationMixedCommittedLower
end
