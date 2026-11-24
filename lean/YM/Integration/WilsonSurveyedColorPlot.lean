import YM.Integration.WilsonSurveyedColorCurvature
import YangMills.WilsonProof.NativeSupport.YM.FVA2.Position.Table

/-! The actual dimensional section of the prescribed MS book, at every
regulator and every field configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorPlot
open Function Labels MS MS.Plane MS.Arts MS.Koszul MS.Landau MS.Native
open MS.Motif MS.Halo MS.Mach MS.Theater MS.Motif.Literal Labels.Taylor
open FVA2.Position.OpenAxis WilsonSurveyedColorTensor WilsonSurveyedColorQuotient
open WilsonSurveyedColorPilot WilsonSurveyedColorCurvature
open scoped Classical BigOperators
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color)
variable {h n m : ℕ} {x : E4} {a b : Axis} {z : ℂ}

def color (h : ℕ) : Module.End ℝ (Labels.Taylor G h) where
  toFun A := ⟨fun i => U.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
    (A.val i), by
      refine ⟨fun i s r => ?_,fun y => ?_⟩
      · exact congrArg U (A.property.1 i s r)
      change ∑ i : Axis, y i • U (A.value i y) = _
      rw [← map_zero U,← A.radial_value y,map_sum]
      simp only [map_smul]⟩
  map_add' A B := by apply Subtype.ext; funext i; ext1; exact map_add U _ _
  map_smul' c A := by apply Subtype.ext; funext i; ext1; exact map_smul U _ _

private theorem sumKeep {J : Type} {F : J → Mield G m} (s : Finset J)
    (hf : ∀ i∈s, Covariant U (F i)) : Covariant U (∑ i∈s, F i) := by
  intro j
  simp_rw [Finset.sum_apply,map_sum]
  rw [Finset.sum_congr rfl (fun k hk => hf k hk j),Finset.sum_comm]
  simp only [Finset.smul_sum]

theorem radial (same : Preserves U) (x : E4) (a : Axis) (z : ℂ) (k : ℕ) :
    Covariant U (Ray G m k z a x) := by
  have derived (a b : Axis) (j : ℕ) : Covariant U (graft (m:=m) z a b x j) := by
    induction j with
    | zero => exact curvature U same z _ _
    | succ j ih =>
      rw [graft]
      exact sumKeep U _ (fun i _ => Covariant.scale U (covariantDerivative U same z _ ih) (x i))
  exact Covariant.scale U (sumKeep U _ (fun i _ => Covariant.scale U (derived i a k) (x i)))
    ((slotDen k)⁻¹:ℝ)

theorem prong (a : Axis) (x : E4) (i : G.ColorIndex) :
    (Prong a x i).comp (color U h) = ∑ j, realEntry U i j • Prong a x j := by
  ext1 X
  change U (X.value a x) i = _
  rw [coordinates,LinearMap.sum_apply]
  rfl

private theorem rampProng (same : Preserves U) (a : Axis) (x : E4) (c : G.ColorIndex) :
    turn U (Ramp G h (asC G h (Prong a x c)) z m) =
      Ramp G h (asC G h ((Prong a x c).comp (color U h))) z m := by
  rw [ramp_Jrad,radial U same x a z h c,prong]
  simp_rw [map_sum,map_smul,Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show realEntry U c j • asC G h (Prong a x j) =
    entry U c j • asC G h (Prong a x j) from rfl,map_smul,Pi.smul_apply,Pi.smul_apply,ramp_Jrad]

private theorem rampScale (c : ℝ) (f : Coord G h) :
    Ramp G h (asC G h (c • f)) z m = (c:ℂ) • Ramp G h (asC G h f) z m := by
  rw [map_smul]
  change Ramp G h ((c:ℂ) • asC G h f) z m = _
  rw [map_smul,Pi.smul_apply,Pi.smul_apply]

theorem ramp (same : Preserves U) (X : Coord G h) :
    turn U (Ramp G h (asC G h X) z m) =
      Ramp G h (asC G h (X.comp (color U h))) z m := by
  have hX : X∈Submodule.span ℝ (Samples G h) := by rw [many]; exact Submodule.mem_top
  refine Submodule.span_induction (p:=fun X _ => turn U (Ramp G h (asC G h X) z m) =
    Ramp G h (asC G h (X.comp (color U h))) z m) ?_ ?_ ?_ ?_ hX
  · rintro _ ⟨a,x,c,rfl⟩
    exact rampProng U same a x c
  · simp only [LinearMap.zero_comp,map_zero,Pi.zero_apply]
  · intro X Y _ _ hx hy
    simp only [map_add,LinearMap.add_comp,Pi.add_apply,hx,hy]
  · intro c X _ hx
    rw [LinearMap.smul_comp,rampScale,rampScale,map_smul,hx]

theorem pigment (same : Preserves U) (f : Labels.Pol G) :
    turn U (seed G f z m) = seed G (Labels.changed (color U) f) z m := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [Labels.changed,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,sightC,← emits,vaultLeaf]
  | add f g hf hg => simp only [map_add,Pi.add_apply,hf,hg]
  | mul_X f i hf =>
    rw [map_mul (Labels.changed (color U)),seed_p,seed_p,productKeep,hf,seed_x,
      show Labels.changed _ (MvPolynomial.X i) = _ from Theater.moved_v (color U) i,
      Vtheta,sampleC,ramp U same]
    rfl

theorem invoiceAt (same : Preserves U) (s : Film0 G h n) :
    turn U (Literal.value (Mob G) z (invoice G h n s) m) =
      seed G (Labels.changed (color U) s.val) z m := by
  rw [priceR,pigment U same]

end YM.Integration.WilsonSurveyedColorPlot
end
