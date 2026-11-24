import YM.Integration.WilsonPositionScaleLawGuardQuadratic

/-! Commutation of the complete printed homogeneous prediction with every genuine grade projection and every fixed inclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardDiagonal
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawDressedTransport (guard)
open WilsonPositionScaleLawGuardSheet (atValue)
open WilsonPositionScaleLawGuardLift (pack)
open WilsonPositionScaleLawGrade (grade reads)
open scoped Topology Classical Asymptotics Polynomial

theorem zeroth {A:Type*}[NormedRing A][NormedAlgebra ℂ A](a:PowerSeries A)(z:ℂ):atValue 0 a z=coeff 0 a:=by
  rw [atValue,WilsonPositionScaleLawGuardEval.printed,show Finset.Iic (0:ℕ)={0} by decide];simp

theorem polynomial {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℂ X][NormedSpace ℂ Y]
    (P:X→ₗ[ℂ]Y)(a:PowerSeries (X→L[ℂ]X))(b:PowerSeries (Y→L[ℂ]Y))
    (functor:∀k v,P (coeff k a v)=coeff k b (P v))(q:ℕ)(z:ℂ)(v:X):
    P (atValue q a z v)=atValue q b z (P v):=by
  induction q with
  | zero=>rw [zeroth,zeroth,functor]
  | succ q ih=>
    rw [WilsonPositionScaleLawGuardQuadratic.nextTerm,WilsonPositionScaleLawGuardQuadratic.nextTerm]
    change P (atValue q a z v+z^(q+1) • (coeff (q+1) a v))=atValue q b z (P v)+z^(q+1) • (coeff (q+1) b (P v))
    rw [P.map_add,P.map_smul,ih,functor]

variable {G:Gauge}{d:ℕ}
theorem homogeneous {A:FieldEnd G d}(closed:Level.Graded A)(i:Fin (d+1))(v:Sec G d):Level.proj i (A v)=A (Level.proj i v):=by
  have pure:=((Level.graded_test A).mp closed)
  calc
    _=Level.proj i (A (∑j:Fin (d+1),Level.proj j v)):=by rw [Level.all]
    _=Level.proj i (A (Level.proj i v)):=by
      rw [map_sum,map_sum,Finset.sum_eq_single i]
      · intro j _ hj
        calc
          _=Level.proj i (Level.proj j (A (Level.proj j v))):=congrArg (Level.proj i) (pure v j).symm
          _=0:=Level.distinct _ i j (Ne.symm hj)
      · simp
    _=_:=pure v i

variable (C:Family G)(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
set_option quotPrecheck false
local notation "E"=>(Bel C.book).Field
include H in
theorem original (s:ℝ)(i:Fin (d+1))(q:ℕ)(z:ℂ)(v:E d):grade C i (atValue q (pack C (guard Z M ν s d)) z v)=atValue q (pack C (guard Z M ν s d)) z (grade C i v):=by
  apply polynomial (grade C i).toLinearMap _ _
  intro k w
  rw [WilsonPositionScaleLawGuardLift.coefficient]
  apply (fields C.labels d).injective
  simp only [ContinuousLinearMap.coe_coe,reads]
  exact homogeneous (WilsonPositionScaleLawDressedTransport.native Z M H ν s d k) i _

theorem upstairs {j k:ℕ}(h:j≤k)(w:E j):fields C.labels k ((scheme C.labels).rise h w)=up h (fields C.labels j w):=
  Subtype.ext (address_rise C.labels k h w)

include H in
theorem inclusion (s:ℝ){j k:ℕ}(h:j≤k)(q:ℕ)(z:ℂ)(v:E j):
    (scheme C.labels).rise h (atValue q (pack C (guard Z M ν s j)) z v)=atValue q (pack C (guard Z M ν s k)) z ((scheme C.labels).rise h v):=by
  apply polynomial ((scheme C.labels).rise h) _ _
  intro n w
  rw [WilsonPositionScaleLawGuardLift.coefficient,WilsonPositionScaleLawGuardLift.coefficient]
  apply (fields C.labels k).injective
  rw [upstairs,reads,reads,upstairs]
  exact (WilsonPositionScaleLawDressedTransport.inclusion Z M H ν s h n _).symm

end YM.Integration.WilsonPositionScaleLawGuardDiagonal
