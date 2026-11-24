import YM.Integration.WilsonSurveyedColorRegulator
import YM.MS.Dial.Slope

/-! Color on the actual scale integral and the unconditioned, separated
multi-source MS hearing. The two one-line identities in the last result
concern its trace and contact kernels before solving the marked hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorHearing
open Function Set Filter Finset MeasureTheory
open MS
open Plane Koszul Heat Flux Landau Detect Tone Latch Latch.Job Rake Arts
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open scoped Classical BigOperators Topology
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) {I W : Type}

def filed : Glade G I →ₗ[ℂ] Glade G I where
  toFun F i s := turn U (F i s)
  map_add' _ _ := funext fun _ => funext fun _ => map_add _ _ _
  map_smul' c F := by
    funext i t
    change turn U (c • F i t) = c • turn U (F i t)
    exact map_smul _ _ _

private theorem killed (w : Legs (Lane4 G)) (F : Law G)
    (gone : ∀ v : Legs (Lane4 G), v.length=w.length → F v=0) : turn U F w = 0 := by
  induction w generalizing F with
  | nil => exact gone [] rfl
  | cons i w ih =>
    change Koszul.D i (turn U F) w = 0
    rw [derivative]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact mul_eq_zero_of_right _ (ih (Koszul.D (MS.Color.setLeg i j) F)
      (fun l h => gone (MS.Color.setLeg i j :: l) (by simp only [List.length_cons,h])))

theorem trained {F : Glade G I} (hF : Job.train false F) :
    Job.train false (filed U F) ∧ filed U (river F) = river (filed U F) := by
  have master (i : I) (s : ℝ) (w : Legs (Lane4 G)) := cent_arguments
    (volume.restrict (Iic s)) ((pilot (D:=Axis) (P:=FourP) U).sense.reaches w)
    (f:=fun t => F i t) (fun l => hF i s l (by simp [Course]))
  constructor
  · intro i s w _
    change Integrable (fun t => turn U (F i t) w) (volume.restrict (Iic s))
    simpa only [emits] using (master i s w).1
  · funext i s w
    change turn U (fun v => ∫ t in Iic s, F i t v) w =
      ∫ t in Iic s, turn U (F i t) w
    simpa only [emits] using (master i s w).2.symm

theorem collection {F : Glade G I} (hc : Rake.collect F) : Rake.collect (filed U F) := by
  obtain ⟨k,hk⟩ := hc
  refine ⟨k,fun i t w len => ?_⟩
  exact killed U w _ fun v hv => hk i t v (hv ▸ len)

theorem step {A B : Calculator G I} {V H : Glade G I} (paid : Trip A V H)
    (line : filed U (A V) = B (filed U V)) :
    Trip B (filed U V) (filed U H) := by
  obtain ⟨history,wage,value⟩ := paid
  obtain ⟨wi,hi⟩ := trained U wage
  rw [map_add,line] at wi hi
  exact ⟨collection U history,wi,(congrArg (filed U) value).trans hi⟩

variable [LinearOrder W]
theorem observed {x : Position W I} {μ : I → Measure QP} {K L : Planet G I}
    {V V' : Site G I} {inlet inlet' : W → Site G I} {X Y : Dance G I W}
    (left : Fields x μ K L V inlet X) (right : Fields x μ K L V' inlet' Y)
    (source : ∀ a k, filed U (inlet a k) = inlet' a k)
    (line : ∀ s : Finset W, 2≤s.card → ∀ k,
      filed U (sailP μ L (X s k)) = sailP μ L (filed U (X s k)))
    (contact : ∀ s : Finset W, 2≤s.card → ∀ k, filed U (multi μ x K L V (X s) X k s) =
      multi μ x K L V' (fun q => filed U (X s q)) (fun t q => filed U (X t q)) k s) :
    (fun t q => filed U (X t q)) = Y := by
  apply Rake.perfect _ right
  refine ⟨?_,?_,?_⟩
  · funext k
    simp [left.1]
  · intro a
    funext k
    change filed U (X {a} k) = inlet' a k
    rw [left.2.1 a]
    exact source a k
  · intro s hs k
    rw [← contact s hs k]
    exact step U (left.2.2 s hs k) (line s hs k)

theorem ordinary {X Y : Dance G I W} (same : (fun t q => filed U (X t q)) = Y)
    (i : I) :
    Puff.Mom.bouquet (fun t q => Vane.blade (X t q) i) =
      Puff.Mom.bouquet (fun t q => Vane.blade (Y t q) i) := by
  subst Y
  rfl

end YM.Integration.WilsonSurveyedColorHearing
end
