import YM.Integration.WilsonPositionScaleLawColorAxis
import YM.Integration.WilsonPhysicalChiralNonfreeCartanOrientation
import YM.Integration.WilsonPhysicalPositionBornTransition

/-! The actual upper Cartan field is an eigenfield for either oriented original
color action on every cumulative quotient. The sign is its physical eigenvalue. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorMark
open Function Maxwell Maxwell.Free XSpace XSpace.Stab XSpace.Stab.OJoint XSpace.Chiral XSpace.Normalize
open PhysMS Spec Table FVA2 FVA2.Dframe
open WilsonPositionThermometerGradedSource (base source)
open WilsonPhysicalChiralNonfreeCartanOrientation (form surveyed)
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornTransition (present)
open WilsonSurveyedColorVacuumKnight (shell)
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ}

def mark (G : Gauge) {d : ℕ} (h : 6 ≤ d) : Sec G d :=
  ⟨(base G 0).val, Free.chain h (base G 0).property⟩

theorem curl (c : Knight G) (X : TaylorTower G) (i : Fin 3) :
    vₜ i (shell c X) = Spin c (vₜ i X) :=
  SchemeConversionRG11.Corona.givens _ _ _

theorem cartan (c : Knight G) (ε : ℝ) (hand : conn c ε) (x y z : G.Color) :
    form (Spin c x) (Spin c y) (Spin c z) = ε * form x y z := by
  calc _ = CH G (Spin c y) (Spin c z) (Spin c x) := real_inner_comm _ _
    _ = ε * CH G y z x := hand y z x
    _ = _ := congrArg (ε * ·) (real_inner_comm _ _)

theorem motion (c : Knight G) (ε : ℝ) (hand : conn c ε) (X : TaylorTower G) :
    Maxwell.probe (shell c X) (base G 0).val = (ε:ℂ) * Maxwell.probe X (base G 0).val := by
  rw [surveyed,surveyed,curl,curl,curl,cartan c ε hand]
  push_cast
  ring

theorem recorded (h : 6 ≤ d) (a : MoveSpace G d) (c : Knight G) (ε : ℝ) (hand : conn c ε)
    (same : records G d (field a (mark G h)) = changing c (records G d (mark G h))) :
    field a (mark G h) = (ε:ℂ) • mark G h := by
  apply Subtype.ext
  apply Maxwell.equalPol
  intro X
  calc Maxwell.probe X (field a (mark G h)).val =
        Maxwell.probe X (appears G d (records G d (field a (mark G h)))) := by rw [opensR]
    _ = Maxwell.probe (shell c X) (mark G h).val := by
      rw [same, WilsonSurveyedColorVacuumKnight.recorded]
    _ = (ε:ℂ) * Maxwell.probe X (mark G h).val := motion c ε hand X
    _ = _ := by change _ = Maxwell.probe X ((ε:ℂ) • (mark G h).val);rw [map_smul,smul_eq_mul]

theorem enrolled (C : Family G) (h : 6 ≤ d) (s : Rose.Badge) (upper : (0 : Fin 3) ∈ s) :
    fields C.labels d ((scheme C.labels).rise h (source C s 0)) = mark G h := by
  apply Subtype.ext
  change address C.labels d ((scheme C.labels).rise h _) = _
  rw [address_rise,address_eval]
  change (fields C.labels 6 ((fields C.labels 6).symm (if (0:Fin 3)∈s then base G 0 else leaf G 6))).val = _
  rw [if_pos upper,LinearEquiv.apply_symm_apply]
  rfl

theorem original (C : Family G) (h : 6 ≤ d) (s : Rose.Badge) (upper : (0 : Fin 3) ∈ s)
    (a : MoveSpace G d) (c : Knight G) (ε : ℝ) (hand : conn c ε)
    (same : records G d (field a (mark G h)) = changing c (records G d (mark G h))) :
    present (C:=C) (field a) ((scheme C.labels).rise h (source C s 0)) =
      (ε:ℂ) • (scheme C.labels).rise h (source C s 0) := by
  apply (fields C.labels d).injective
  rw [map_smul]
  change (fields C.labels d) ((fields C.labels d).symm
    (field a ((fields C.labels d) ((scheme C.labels).rise h (source C s 0))))) = _
  rw [LinearEquiv.apply_symm_apply,enrolled C h s upper]
  exact recorded h a c ε hand same

end YM.Integration.WilsonPositionScaleLawColorMark
end
