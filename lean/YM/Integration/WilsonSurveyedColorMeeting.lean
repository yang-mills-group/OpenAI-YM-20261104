import YM.Integration.WilsonSurveyedColorHearing
import YM.MS.Latch.Clan

/-! The phase, Koszul sign and two oriented derivative legs at a genuinely
separated contact in the MS position-space flow. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorMeeting
open Function Set Finset MeasureTheory
open MS
open Plane Koszul Heat Flux Landau Detect Tone Latch Latch.Job Rake Arts
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open WilsonSurveyedColorFlow
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
local notation "I" => G.ColorIndex
local notation "Ψ" => field (Landau.parity (A:=Axis) (C:=G.ColorIndex))

def phased (A : QP) : Law G →ₗ[ℂ] Law G where
  toFun F l := Tone.bill A (net l) * F l
  map_add' _ _ := funext fun _ => mul_add _ _ _
  map_smul' _ _ := funext fun _ => mul_left_comm _ _ _

theorem phasedColor (A : QP) (F : Law G) : turn U (phased A F) = phased A (turn U F) := by
  funext l
  let c := Tone.bill A (net l)
  have same (v : Legs (Lane4 G)) (hv : net v = (pilot (D:=Axis) (P:=QP) U).volp (net l)) :
      phased A F v = (c • F) v := by
    change Tone.bill A (net v) * F v = Tone.bill A (net l) * F v
    rw [show net v = net l from hv]
  have h := (pilot U).offset (phased A F) (c • F) (net l) l same rfl
  rw [emits,map_smul] at h
  exact h

def vertex (A : QP) (b : Bool) : Law G →ₗ[ℂ] Law G →ₗ[ℂ] Law G :=
  (product Ψ).comp ((phased A).comp (sign Ψ b))

theorem vertexColor (A : QP) (b : Bool) (F H : Law G) :
    turn U (vertex A b F H) = vertex A b (turn U F) (turn U H) := by
  have signH : turn U (sign Ψ b F) = sign Ψ b (turn U F) := by
    simpa only [emits] using (pilot U).beam_sign F b
  change turn U (product Ψ (phased A (sign Ψ b F)) H) = _
  rw [← emits,(pilot U).circle_prod,emits,phasedColor,signH]
  rfl

private theorem joined {X Y Z : Type} [AddCommMonoid X] [Module ℂ X]
    [AddCommMonoid Y] [Module ℂ Y] [AddCommMonoid Z] [Module ℂ Z]
    (P : X →ₗ[ℂ] Y →ₗ[ℂ] Z) (f : I → X) (g : I → Y) :
    ∑ i, P (∑ a, entry U a i • f a) (∑ b, entry U b i • g b) = ∑ j, P (f j) (g j) := by
  simp only [map_sum,map_smul,LinearMap.smul_apply,LinearMap.sum_apply,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul,across]
  simp [ite_smul]

def pair (A q : QP) (a b : Atom Axis) (F H : Law G) : Law G :=
  ∑ c : I, vertex A (Landau.p b) (Koszul.D ((a,c),q) F) (Koszul.D ((b,c),-q) H)

theorem pairColor (A q : QP) (a b : Atom Axis) (F H : Law G) :
    turn U (pair A q a b F H) = pair A q a b (turn U F) (turn U H) := by
  unfold pair
  rw [map_sum]
  simp_rw [vertexColor U,derivative U]
  exact (joined U (vertex A (Landau.p b)) (fun c => turn U (Koszul.D ((a,c),q) F))
    (fun c => turn U (Koszul.D ((b,c),-q) H))).symm

def incoming (A q : QP) (K : City.YMflow Axis) (F H : Law G) : Law G :=
  ∑ a, ∑ b, (Tone.bill A q * (2 * K a b q)) • pair A q a b F H

theorem incomingColor (A q : QP) (K : City.YMflow Axis) (F H : Law G) :
    turn U (incoming A q K F H) = incoming A q K (turn U F) (turn U H) := by
  simp only [incoming,map_sum,map_smul,pairColor]

end YM.Integration.WilsonSurveyedColorMeeting
end
