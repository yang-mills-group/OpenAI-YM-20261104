import YM.Integration.WilsonThermometerMixedAmplitude
import YM.Integration.WilsonFiniteGalleryHaar
import YM.MergeProof.Wicket

/-! The original Haar kernel propagates the two amplitudes on their entire
incoming polynomial, including the old quiet and its nonconstant exterior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedKernel
open Finset Lattice RG Wilson Marker MeasureTheory MergeProof.Accent WilsonThermometerMixedAmplitude
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

theorem original {G : Gauge} {c f : Side} {β : ℝ} (S : StepData c f) (kernel : S.IsKernel β G)
    (q : ℂ) (A Y F : Config G f → Poly (J))
    (erased : Integrable A (prior G f)) (raised : Integrable F (prior G f))
    (line : ∀ U, Line q (A U) (Y U) (F U)) :
    Integrable Y (prior G f) ∧
    ∀V, Line q (S.push β A V) (S.push β Y V) (S.push β F V) := by
  let coord (B : Config G f → Poly (J)) (s:(J).Mode) := fun U => (B U).part s
  have expansion (s:(J).Mode) : coord Y s = (1-q) • coord A s + q • coord F s := by
    funext U
    dsimp [coord]
    rw [(line U).value]
    change (A U).part s + q*((F U).part s-(A U).part s) = (1-q)*(A U).part s+q*(F U).part s
    ring
  have ra (s:(J).Mode) : Integrable (coord A s) (prior G f) := (Poly.get s).integrable_comp erased
  have rf (s:(J).Mode) : Integrable (coord F s) (prior G f) := (Poly.get s).integrable_comp raised
  have ry : Integrable Y (prior G f) := by
    apply integrable_pi_iff.mpr
    intro s
    change Integrable (coord Y s) _
    rw [expansion]
    exact ((ra s).smul (1-q)).add ((rf s).smul q)
  refine ⟨ry,fun V=>?_⟩
  constructor
  · intro s hs
    have equal : coord F s = coord A s := by
      funext U
      exact sub_eq_zero.mp ((line U).marked s hs)
    change (S.push β F V).part s-(S.push β A V).part s=0
    apply sub_eq_zero.mpr
    rw [congrFun (push_get kernel raised s) V,congrFun (push_get kernel erased s) V]
    exact congrFun (congrArg (S.push β) equal) V
  · ext1 s
    have summed := congrFun (S.push_add kernel ((1-q) • coord A s) (q • coord F s)
      ((ra s).smul (1-q)) ((rf s).smul q)) V
    rw [S.push_smul _ β _ (ra s),S.push_smul _ β _ (rf s)] at summed
    have price := congrFun (congrArg (S.push β) (expansion s)) V
    change (S.push β Y V).part s=(S.push β A V).part s+q*((S.push β F V).part s-(S.push β A V).part s)
    rw [congrFun (push_get kernel ry s) V,congrFun (push_get kernel erased s) V,congrFun (push_get kernel raised s) V]
    change S.push β (coord Y s) V=S.push β (coord A s) V+q*(S.push β (coord F s) V-S.push β (coord A s) V)
    rw [price,summed]
    change (1-q)*(S.push β (coord A s) V)+q*(S.push β (coord F s) V)=_
    ring
end YM.Integration.WilsonThermometerMixedKernel
end
