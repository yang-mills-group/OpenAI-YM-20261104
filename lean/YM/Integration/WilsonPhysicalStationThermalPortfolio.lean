import YM.Integration.WilsonPhysicalStationThermalFiledPair

/-! Expand a cutoff-dependent nominated physical vector on its actual finite
quotient before applying the two-arm estimate. Conjugate the coefficient
at the physical adjoint and leave the other arm and its sites fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalPortfolio
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph Maxwell.Free
open Further.CorrectedLift (ladder)
open WilsonPhysicalPositionReflectedReturn (ports)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalPair (cell raw)
open scoped BigOperators Classical
variable {G:Gauge}(C:Family G){d:ℕ}
local notation "F"=>C.labels.level d

def scalar (e:Fin 2)(x:ℂ):ℂ:=if e=0 then x else star x

theorem columns (w:(Cells.standard C).Field d):
    w=∑i,(ladder C d w i) • (Cells.standard C).project d (Pi.single i 1):=by
  let y:=ladder C d w
  let projection:C.label d→ₗ[ℂ](Cells.standard C).Field d:=(Cells.standard C).project d
  change w=∑i,y i•projection (Pi.single i 1)
  have expand:(∑i,y i•(Pi.single i 1:C.label d))=y:=by
    funext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  calc w = projection y := (Further.CorrectedLift.ladder_reads w).symm
       _ = projection (∑i,y i•(Pi.single i 1:C.label d)) := congrArg _ expand.symm
       _ = _ :=by rw [map_sum];exact Finset.sum_congr rfl fun i _=>projection.map_smul _ _

theorem turned (w:(Cells.standard C).Field d)(s:Signed)(e:Fin 2):
    ports (C:=C) w s e=∑i,scalar e (ladder C d w i) • probe C i s e:=by
  let spin:=(Cells.standard C).mirror (spin_free C.labels) d s
  let adj:=(Cells.standard C).adj (spin_free C.labels) d 0
  have forward:spin w=∑i,ladder C d w i • spin ((Cells.standard C).project d (Pi.single i 1)):=calc
    _=spin (∑i,ladder C d w i • (Cells.standard C).project d (Pi.single i 1)):=congrArg spin (columns C w)
    _=_:=by rw [map_sum];simp only [map_smul]
  fin_cases e
  · exact forward
  · change adj (spin w)=∑i,star (ladder C d w i) • adj (spin ((Cells.standard C).project d (Pi.single i 1)))
    rw [forward,map_sum]
    simp only [map_smulₛₗ,starRingEnd_apply]

variable (R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D:ℕ}(V:Vane R.family D)(rank:Fin (D+1)){N p:ℕ}
    (checked:V.checked f H D)(top:V.k<N)
    (j:ℕ)(o:Fin 2 → Cover)(y:Points 2)(x:R.family.label rank)

def residual (w:(Cells.standard R.family).Field rank):ℂ:=
  cell R V rank (p:=p) checked top j o x w-
    (Cells.standard R.family).classMoment (Cells.standard R.family) (fun _:Fin 2=>rank.val) y
      ![(Cells.standard R.family).project rank x,w]

private theorem replacing {E:Type*}[Zero E](x v:E):
    Function.update (![x,0]:Fin 2 → E) 1 v=![x,v]:=by
  funext i
  fin_cases i <;>simp [Function.update]

theorem original {I:Type*}[Fintype I](amps:I→ℂ)(fields:I→(Cells.standard R.family).Field rank):
    residual R V rank (p:=p) checked top j o y x (∑i,amps i•fields i)=
      ∑i,amps i*residual R V rank (p:=p) checked top j o y x (fields i):=by
  let M:=R.family.ensemble (N:=N) (p:=p) (fun _:Fin 2=>rank.val) (fun i=>location R.family.S j N p (o i))
  let G0:=(Cells.standard R.family).classMoment (Cells.standard R.family) (fun _:Fin 2=>rank.val) y
  let xr:=raw R V rank (p:=p) checked top x
  let onShell:=(Cells.standard R.family).project rank x
  let fee:((Cells.standard R.family).Field rank)→ₗ[ℂ]ℂ:=
      (M.toLinearMap ![xr,0] 1).comp (V.wheel.atCut (N,p) rank).toLinearMap - G0.toLinearMap ![onShell,0] 1
  have read (w:(Cells.standard R.family).Field rank):fee w=residual R V rank (p:=p) checked top j o y x w:=by
    change M (Function.update (![xr,0]:Fin 2 → R.family.label rank) 1 _) -
      G0 (Function.update (![onShell,0]:Fin 2 → (Cells.standard R.family).Field rank) 1 w)=
      M ![xr,(V.wheel.atCut (N,p) rank) w]-G0 ![onShell,w]
    rw [replacing,replacing];rfl
  rw [←read,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp_rw [read]

end YM.Integration.WilsonPhysicalStationThermalPortfolio
end
