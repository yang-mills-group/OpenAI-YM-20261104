import YM.Integration.WilsonPositionGradedThermometerGround
import YM.XSpace.OffAxis
import YM.XSpace.Laurel

/-! The two constant coefficients used when the measured upper field is
reduced against the original lower fields. The two-point diagnostic is
zero at every separated placement. The three-point coefficient uses the
original Rose test on the two actual signed-equivariant lower columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedSchurFree
open Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress RG17 PhysMS Lattice Wilson RG PhysicalNext.Repeat.Legato
open Function Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Structure1 XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerOriginal
open WilsonPositionGradedThermometerGround Table Spec
open private moved from YM.Integration.WilsonPositionGradedThermometerGround
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {V:Store G}

def pair (e:Sec G 4) (i:Fin 2):Sec G 6:=if i=0 then Rose.toll G else up (by decide : 4≤6) e

theorem two (simple:G.Simple) (e:Sec G 4) (x:Points 2) (hx:x∈conf 2):
    scene x 6 (pair e)=0 := by
  have even :hinge 6 (up (by decide : 4≤6) e)=up (by decide : 4≤6) e:=
    Subtype.ext (AxesTangent.same_low simple e.val e.property)
  have eqn : hinge 6 ∘ pair e = Function.update (pair e) 0 (-(pair e 0)) := by
    funext i
    fin_cases i
    · simp only [Function.comp_apply]
      exact Rose.t_odd
    · simp only [Function.comp_apply]
      exact even
  have h:scene x 6 (hinge 6 ∘ pair e)=scene x 6 (pair e):=Normalize.free_symmetry _ hx
  rw [eqn,MultilinearMap.map_update_neg,Function.update_eq_self] at h
  linear_combination -h/2

theorem triangle (simple:G.Simple) (K:Rose.Pick V) (A:Group C 6) (spin:(Bel C.book).RealSpin)
    (coherent:Coherent spin spin 4 (A.change 4)) (e:Sec G 4):
    (Rose.test K).applyTo (fun x=>WilsonMaxwellThermometerFaces.connected x
      (Graph3.trip (up (by decide : 4≤6) e)
        (up (by decide : 4≤6) (transform A 4 (WilsonMaxwellThermometerOriginal.lower G)))
        (up (by decide : 4≤6) (transform A 4 (WilsonMaxwellThermometerOriginal.lower G)))))=0 :=
  WilsonMaxwellThermometerOriginal.moved simple K _ _ (moved A 4 spin coherent)

end YM.Integration.WilsonMaxwellThermometerNominatedSchurFree
