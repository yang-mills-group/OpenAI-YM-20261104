import YM.Integration.WilsonMaxwellThermometerPublicGalop
import YM.XSpace.Vanilla
import YM.XSpace.Welcome

/-! At each admitted finite position regulator, the first thermometer coefficient
hears only the factor-odd part of its upper leg. The lower legs may be any
actual cap-four columns, including their unit parts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicEvenSlope
open Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress RG17 PhysMS PhysMS.Frame
open Function Filter Lattice Maxwell Maxwell.Free RG Wilson PhysicalNext.Repeat.Legato
open XSpace XSpace.Structure1 XSpace.Cirrus XSpace.Normalize XSpace.Retirement XSpace.Photo XSpace.Graph3 XSpace.Rose
open WilsonMaxwellThermometerPublicGalop WilsonMaxwellThermometerInteracting WilsonMaxwellThermometerFirstDetector
open WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionGradedThermometerGround
open scoped Classical BigOperators Topology
variable {G:Gauge} (W:Initialize G) {V:Normalize.Store G}

def entered (b:Sec G 6) (u v:Sec G 4):Tags G 6 3 :=
  trip b (up (by decide:4≤6) u) (up (by decide:4≤6) v)

theorem face (simple:G.Simple)(x:Sample 3)(stage:V.Meets W x.F 6)
    (a:Sec G 6)(even:hinge 6 a=a)(u v:Sec G 4)(S:Finset (Fin 3)):
    quotient W (V:=V) x (entered a u v) 1 S=0:=by
  have lo (t:Sec G 4):hinge 6 (up (by decide:4≤6) t)=up (by decide:4≤6) t:=
    Subtype.ext (AxesTangent.same_low simple t.val t.property)
  let p:=missing (entered a u v) S
  have eqn:hinge 6 ∘ p=p:=by
    funext i
    fin_cases i <;>simp [p,missing,entered,XSpace.Graph3.trip,apply_ite,hinge_leaf,even,lo] <;> split <;> simp_all
  have eq:=cooksV W V 6 x p 1 stage
  rw [eqn] at eq
  rw [show quotient W (V:=V) x (entered a u v) 1 S = cooked W V 6 x 1 p by
    symm; apply detail]
  have neg:cooked W V 6 x 1 p= -cooked W V 6 x 1 p:=by simpa using eq
  linear_combination neg/2

theorem disappears (simple:G.Simple)(x:Sample 3)(stage:V.Meets W x.F 6)
    (a:Sec G 6)(even:hinge 6 a=a)(u v:Sec G 4):
    node W (V:=V) x (entered a u v)=0:=by
  simp only [node,first,face W simple x stage a even u v]
  ring

theorem coefficient (simple:G.Simple)(x:Sample 3)(stage:V.Meets W x.F 6)
    (b a:Sec G 6)(even:hinge 6 a=a)(u v:Sec G 4):
    node W (V:=V) x (entered (b+a) u v)=node W (V:=V) x (entered b u v):=by
  have edit (t:Sec G 6):Function.update (entered b u v) 0 t=entered t u v:=by
    funext j; fin_cases j <;> rfl
  have eq:sampled W (V:=V) x (entered (b+a) u v)=
      sampled W (V:=V) x (entered b u v)+sampled W (V:=V) x (entered a u v):=by
    rw [←edit (b+a),(sampled W (V:=V) x).map_update_add,edit,edit]
  simpa only [enrolled,disappears W simple x stage a even u v,add_zero] using eq

variable (R:Run G) (K:Rose.Pick V)(simple:G.Simple)(B:ℕ)
local notation "k" => WilsonMeasuredWindow.stop R.family.path.levels simple B
local notation "μ"=>fun (r:ℝ)(per:ℕ)=>chart R (k r) per (spacing R simple B r) (positive R simple B r)

theorem original (hB:0<B)(f:Extraction.Order)(Y:Filter (ℕ×ℕ))(prior:Y≤f.fuse):
    ∀ᶠ w:ℝ×(ℕ×ℕ) in (trail.curry Y),
    ∀ (b a:Sec G 6), hinge 6 a=a → ∀u v:Sec G 4,
      report R W K simple B w.1 w.2 (entered (b+a) u v) =
        report R W K simple B w.1 w.2 (entered b u v):=by
  have geo:=reporting R trail f Y prior k _ (positive R simple B) (shrinking R simple B hB)
  have ready:∀ᶠ m in Front,V.Meets W m 6:=(V.nested_solution W 6 Cirrus.frontier).2.mono fun _ h=>h.1
  filter_upwards [geo.eventually ready] with w stage b a even u v
  by_cases h:k w.1≤w.2.1
  · simp only [report,dif_pos h]
    apply Finset.sum_congr rfl
    intro o _
    apply congrArg (fun z:ℂ=>weight (Rose.test K) (positions (R:=R) w.1 w.2) o • z)
    let m:=μ w.1 w.2.2
    let x:=WilsonMaxwellThermometerShiftedPanel.translated m
      (Mesh.back m ((R.family.S.toDepth h w.2.2).parent ∘ o))
    exact coefficient W simple x stage b a even u v
  · simp only [report,dif_neg h]

end YM.Integration.WilsonMaxwellThermometerPublicEvenSlope
end
