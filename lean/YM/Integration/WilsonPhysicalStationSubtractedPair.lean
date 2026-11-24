import YM.Integration.WilsonMovingForkReporterBothArms
import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins

/-! Read the actual finite Wilson pair on two previously filed physical arms after subtracting a finite portfolio of original lower terminals. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationSubtractedPair
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {ℓ:Ultrafilter (ℕ×ℕ)} {d:ℕ} {I:Type*} [Fintype I]

def lower (c:I→ℂ)(w:I→(ℕ×ℕ)→R.family.label d)(p:ℕ×ℕ):R.family.label d:=
  ∑i,c i • (R.family.factory d p.1 p.2).terminal (w i p)

include F in
theorem original (simple:G.Simple)(below:(ℓ:Filter _)≤f.fuse){x y:S.Field d}
    (X:Arm R.family S (ℓ:Filter _) d x)(Y:Arm R.family S (ℓ:Filter _) d y)
    (c:I→ℂ)(w:I→(ℕ×ℕ)→R.family.label d)(v:I→R.family.label d)
    (converges:∀i,Tendsto (fun p:ℕ×ℕ=>(R.family.factory d p.1 p.2).terminal (w i p))
      (ℓ:Filter _) (𝓝 (v i)))(j:ℕ)(o:Fin 2 → Cover)(safe:Extraction.Order.grid R.family j o∈conf 2):
    Tendsto (fun p:ℕ×ℕ=>WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) (fun _:Fin 2=>d) j o
      p.1 p.2 ![X.source p-lower R c w p,Y.source p]) (ℓ:Filter _)
      (𝓝 (S.classMoment S (fun _:Fin 2=>d) (Extraction.Order.grid R.family j o)
        ![x-S.project d (∑i,c i • v i),y])):=by
  let labels:(ℕ×ℕ)→R.family.book.Vector (fun _:Fin 2=>d):=fun p=>![X.source p-lower R c w p,Y.source p]
  let limits:R.family.book.Vector (fun _:Fin 2=>d):=![X.label-∑i,c i • v i,Y.label]
  have low:Tendsto (lower R c w) (ℓ:Filter _) (𝓝 (∑i,c i • v i)):=
    tendsto_finsetSum _ (fun i _=>(converges i).const_smul (c i))
  have move(i:Fin 2):Tendsto (fun p=>labels p i) (ℓ:Filter _) (𝓝 (limits i)):=by
    fin_cases i
    · exact X.approaches.sub low
    · exact Y.approaches
  have fields:(fun i:Fin 2=>S.project d (limits i))=![x-S.project d (∑i,c i • v i),y]:=by
    funext i
    fin_cases i
    · change S.project d (X.label-∑i,c i • v i)=_
      rw [map_sub,X.represents]
      rfl
    · exact Y.represents
  have saved:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) (fun _:Fin 2=>d) safe limits
  rw [←fields,saved]
  exact WilsonMeasuredPublicEntranceSeparatedPins.variation R F _ j o simple below labels limits move safe

end YM.Integration.WilsonPhysicalStationSubtractedPair
end
