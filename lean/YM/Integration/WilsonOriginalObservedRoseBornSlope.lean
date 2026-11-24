import YM.Integration.WilsonOriginalObservedRoseBornPosition
import YM.Integration.WilsonMaxwellThermometerFirstDetector

/-! The constant and the linear response of the seven proper/whole finite Galop targets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornSlope
open Finset Filter PowerSeries Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose
open FVA2 FVA2.Register MS MS.WilsonBridge.Coupling
open WilsonMaxwellThermometerPublicGalop (quotient node)
open WilsonOriginalObservedRoseFiniteReturn (row target)
open WilsonOriginalObservedRoseBornLedger (center)
open WilsonPositionThermometerConnected (value)
open scoped Classical BigOperators Topology
variable {G:Gauge}(D:Initialize G){V:Store G}(x:Sample 3)(p:Tags G 6 3)(g:ℂ)

private theorem linear (A:PowerSeries ℂ):((PowerSeries.trunc (1+1) A).eval g)=coeff 0 A+g*coeff 1 A:=by
  rw [PowerSeries.trunc_succ,Polynomial.eval_add,Polynomial.eval_monomial]
  simp [PowerSeries.trunc_apply,mul_comm]

theorem ordinary (s:Badge):row D (V:=V) x p 1 g s=quotient D (V:=V) x p 0 s+
    g*quotient D (V:=V) x p 1 s:=by
  unfold row WilsonOriginalObservedRoseTruncatedFaces.face
  rw [linear]
  simp only [WilsonOriginalObservedRoseProgram.face,PowerSeries.coeff_mk]

theorem connected:target D (V:=V) x p 1 g=value (quotient D (V:=V) x p 0)+g*node D (V:=V) x p:=by
  unfold target
  rw [linear,WilsonOriginalObservedRoseProgram.constant,WilsonOriginalObservedRoseProgram.slope]

variable (Z:WilsonPrescription G){Y:Type}[Fintype Y](μ:Y→ℂ)(sites:Y→Sample 3)

def ground:ℂ:=∑y,μ y*value (quotient Z.scheme (V:=Z.store) (sites y) (tag G) 0)
def coefficient:ℂ:=∑y,μ y*node Z.scheme (V:=Z.store) (sites y) (tag G)

theorem original (m:Mesh)(t:ℝ):
    (∀(s:Badge)(y:Y),row Z.scheme (V:=Z.store) (sites y) (tag G) 1 (t:ℂ) s =
      quotient Z.scheme (V:=Z.store) (sites y) (tag G) 0 s+
      (t:ℂ)*quotient Z.scheme (V:=Z.store) (sites y) (tag G) 1 s) ∧
    (center Z.scheme (V:=Z.store) μ sites (tag G) 1 (t:ℂ)).re-
        WilsonMaxwellThermometerKineticCoordinate.printed Z m 1 t =
      ((ground Z μ sites).re-WilsonMaxwellThermometerKineticCoordinate.ground Z m)+
      t*((coefficient Z μ sites).re-(coeff 1 (Detector Z.scheme Z.criterion m)).re):=by
  refine ⟨fun s y=>ordinary Z.scheme (sites y) (tag G) t s,?_⟩
  have c:center Z.scheme (V:=Z.store) μ sites (tag G) 1 (t:ℂ)=
      ground Z μ sites+(t:ℂ)*coefficient Z μ sites:=by
    simp only [center,ground,coefficient,connected,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    exact congrArg _ (Finset.sum_congr rfl (fun y _=>by ring))
  rw [c,Complex.add_re,Complex.re_ofReal_mul]
  simp [WilsonMaxwellThermometerKineticCoordinate.printed,WilsonMaxwellThermometerKineticCoordinate.ground,
    Fin.sum_univ_two]
  ring

theorem calibrated (simple:G.Simple):
    Tendsto (fun m=>coeff 1 (Detector Z.scheme Z.criterion m)) Front (𝓝 ((c_T Z.criterion:ℝ):ℂ)) :=
  XSpace.Rose.diagnosed Z.scheme Z.criterion simple

end YM.Integration.WilsonOriginalObservedRoseBornSlope
