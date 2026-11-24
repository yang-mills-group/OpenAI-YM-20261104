import YM.Integration.OriginalMarkedConditionalAction
import YM.Integration.SignedWeightedMoment
import YM.Progress.DIRECTED_RECIPE.Normalization
import YM.Push.GRID_APPROXIMATION.KernelBasic

/-! Local marked conditional reads at an interior date of the original
Wilson evolution, with the same downstream field and full forced action. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonHeldRetainedAction

open Function MeasureTheory Lattice RG Wilson
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open OriginalMarkedConditionalAction OriginalMarkedRunAction
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (N per j : ℕ)
local notation "fine" => Config G (R.family.side (j+1) per)
local notation "coarse" => Config G (R.family.side j per)
local notation "haar" => prior G (R.family.side (j+1) per)
local notation "step" => R.family.path.levels.clock.op j per
local notation "β" => R.family.path.β N per (j+1)

def kernel (S : Support (R.family.side (j+1) per)) (outside : fine) (V : coarse)
    (U : fine) : ℝ := (step).density β (OriginalMarkedConditionalAction.patch S outside U) V

def reference (S : Support (R.family.side (j+1) per)) (outside : fine) (V : coarse) :
    Measure fine := SignedWeightedMoment.normalized haar (kernel R N per j S outside V)

private theorem positive_reference {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (k : X → ℝ) (e : Envelope k) (hk : ∀ x, 0 < k x) :
    IsProbabilityMeasure (SignedWeightedMoment.normalized μ k) := by
  apply SignedWeightedMoment.mass_one μ e (fun x => (hk x).le)
  apply (integral_pos_iff_support_of_nonneg (fun x => (hk x).le) (e.integrable μ)).mpr
  rw [show Function.support k = Set.univ from Set.eq_univ_of_forall fun x => (hk x).ne']
  simp

private theorem kernel_envelope {c f : Side} (K : StepData c f) (α : ℝ)
    (hK : K.patch.Branches K.kernel G) (V : Config G c) :
    Envelope (fun U : Config G f => K.density α U V) := by
  have pair : Measurable (fun U : Config G f => (U,V)) := measurable_id.prodMk measurable_const
  exact Envelope.comp_env (f:=fun Z : Config G f × Config G c => K.density α Z.1 Z.2)
    (g:=fun U : Config G f => (U,V)) (Push.GridApprox.den_env (K.isKernel hK α)) pair

private theorem compose {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {k : X → ℝ} (e : Envelope k) (ξ : Y → X) (mx : Measurable ξ) :
    Envelope (fun y => k (ξ y)) :=
  ⟨e.meas.comp mx,e.cost.imp fun _ h y => h (ξ y)⟩

private theorem weighted_haar {c f : Side} (K : StepData c f) (α : ℝ)
    (hK : K.patch.Branches K.kernel G) (ξ : Config G f → Config G f) (mξ : Measurable ξ)
    (V : Config G c) :
    IsProbabilityMeasure (SignedWeightedMoment.normalized (prior G f) (fun U => K.density α (ξ U) V)) :=
  positive_reference (prior G f) (fun U => K.density α (ξ U) V)
    (compose (kernel_envelope K α hK V) ξ mξ) (fun U => Progress.DirectedRecipe.density_strict K α hK (ξ U) V)

theorem probability (S : Support (R.family.side (j+1) per)) (outside : fine) (V : coarse) :
    IsProbabilityMeasure (reference R N per j S outside V) :=
  weighted_haar (step) β (R.family.path.levels.blocks j per).branches
    (OriginalMarkedConditionalAction.patch S outside) (measurable_patch S outside) V

/-- Both positive marked readings use the same original K(U,V) and
product Haar. Each action still contributes its own conditional mass. -/
def reading (S : Support (R.family.side (j+1) per)) (outside : fine) (V : coarse)
    (P : Rep G (R.family.side (j+1) per)) (f : fine → ℂ) : ℂ :=
  OriginalMarkedRowCovariance.read (reference R N per j S outside V)
    (fun U => P.eval (OriginalMarkedConditionalAction.patch S outside U)) (fun U => f (OriginalMarkedConditionalAction.patch S outside U))

/-- The error for the whole signed product on all fields, before
enlarging the loop order or integrating any exterior slot. -/
theorem product {ι : Type*} (d : ℕ) (live : j+1<N)
    (A : Comparison R (p:=per) live d) (S : Support (R.family.side (j+1) per))
    (outside : fine) (V : coarse) (F : ι → fine → ℂ)
    (mf : ∀ i,Measurable (F i)) (b : ι → ℝ) (hb : ∀ i,0≤b i)
    (cap : ∀ i U,‖F i U‖≤b i) (s : Finset ι) :
    let a := OriginalMarkedLocalPurchase.fee R.alloy.B.a (j+1) S
      ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per ((j+1)+1))^(d+1))
    let Fₛ := fun U => ∏ i ∈ s,F i U
    ‖reading R N per j S outside V (R.family.path.rep N per (j+1)) Fₛ -
      reading R N per j S outside V (approximation R (p:=per) live d) Fₛ‖ ≤
      2*Real.exp (2*a)*a*(∏ i ∈ s,b i) := by
  classical
  letI := probability R N per j S outside V
  apply OriginalMarkedConditionalAction.fiber R live (reference R N per j S outside V)
    A S outside (OriginalMarkedConditionalAction.patch S outside) (measurable_patch S outside)
    (OriginalMarkedConditionalAction.outside S outside) _
    (Finset.measurable_fun_prod s (fun i _ => mf i)) _ (Finset.prod_nonneg fun i _ => hb i)
  intro U
  rw [norm_prod]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => cap i U)

end YM.Integration.WilsonHeldRetainedAction

