import YM.Integration.WilsonPhysicalStationThermalCoordinates
import YM.Integration.WilsonPhysicalStationElectedEars

/-! Reassemble the full Wilson source of a nominated physical vote on its own reporter. Each correction belongs to its actual top-engineering axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFullVote
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open Labels Next.Rank Next.Rank.East Next.Rank.Price MeasureTheory Trace MergeProof.East
open Trace.Terrace Trace.Over FVA2 FVA2.Register Trace.Physical.GermGraph Further.CorrectedLift
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationThermalCoordinates (word)
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonPhysicalStationTableJump (pair)
open scoped Topology Classical BigOperators Matrix

variable {G:Gauge}(C:Family G)(h:ℕ)
abbrev Head:= {a:(C.labels.level h).Index // ((C.labels.level h).grades a).1=h}
abbrev Below:= {a:(C.labels.level h).Index // ¬((C.labels.level h).grades a).1=h}

variable (R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{D:ℕ}(B:Vane R.family D)
    {h:ℕ}(db:h<D+1)(cb:B.checked f H D){N per:ℕ}(top:B.k<N)
set_option quotPrecheck false
local notation "axis" => (R.family.labels.level h).Index

def principal (w:Head R.family h→(ℕ×ℕ)→R.family.label h)(j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label h)(i:Head R.family h):ℂ:=
  pair R ⟨h,db⟩ N per j o (raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1)-
    (R.family.factory h N per).terminal (w i (N,per))) peer

def lowerRow (j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label h)(i:Below R.family h):ℂ:=
  pair R ⟨h,db⟩ N per j o (raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1)) peer

theorem source (x:R.family.label h)(w:Head R.family h→(ℕ×ℕ)→R.family.label h):
    raw R B ⟨h,db⟩ (p:=per) cb top x-lower R (fun i:Head R.family h=>x i.val) w (N,per)=
      (∑i:Head R.family h,x i.val • (raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1)-
        (R.family.factory h N per).terminal (w i (N,per))))+
      ∑i:Below R.family h,x i.val • raw R B ⟨h,db⟩ (p:=per) cb top (Pi.single i.val 1):=by
  classical
  let W:=word R B ⟨h,db⟩ (p:=per) cb top
  have decompose:(∑i:axis,x i • (Pi.single i 1:R.family.label h))=x:=by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  have split:=Fintype.sum_subtype_add_sum_subtype (fun i:axis=>((R.family.labels.level h).grades i).1=h)
    (fun i:axis=>x i • W (Pi.single i 1))
  have full:W x=(∑i:Head R.family h,x i.val • W (Pi.single i.val 1))+
      ∑i:Below R.family h,x i.val • W (Pi.single i.val 1):=by
    rw [split,←decompose]
    rw [map_sum]
    simp only [map_smul,decompose]
  change W x-_=(∑i:Head R.family h,x i.val • (W (Pi.single i.val 1)-_))+∑i:Below R.family h,x i.val • W (Pi.single i.val 1)
  rw [full]
  simp only [smul_sub,Finset.sum_sub_distrib,lower]
  abel

theorem original (u:(Bel R.family.book).Field h)(w:Head R.family h→(ℕ×ℕ)→R.family.label h)
    (j:ℕ)(o:Fin 2 → Cover)(peer:R.family.label h):
    let x:=ladder R.family h u
    pair R ⟨h,db⟩ N per j o (B.wheel.atCut (N,per) ⟨h,db⟩ u-lower R (fun i:Head R.family h=>x i.val) w (N,per)) peer=
      (∑i:Head R.family h,x i.val*principal R B db (per:=per) cb top w j o peer i)+
      ∑i:Below R.family h,x i.val*lowerRow R B db (per:=per) cb top j o peer i:=by
  intro x
  let M:=R.family.ensemble (N:=N) (p:=per) (fun _:Fin 2=>h) (fun i=>location R.family.S j N per (o i))
  let L:R.family.label h→ₗ[ℂ]ℂ:=M.toLinearMap ![0,peer] 0
  have applied (y:R.family.label h): L y=pair R ⟨h,db⟩ N per j o y peer:=by
    change M (Function.update ![0,peer] 0 y)=M ![y,peer]
    exact congrArg _ (funext fun i=>by fin_cases i <;>simp [Function.update])
  rw [←applied,←WilsonPhysicalStationThermalPair.lifted R B ⟨h,db⟩ cb top u,source R B db cb top x w]
  simp only [map_add,map_sum,map_smul,smul_eq_mul]
  simp only [applied,principal,lowerRow]

end YM.Integration.WilsonPhysicalStationFullVote
end
