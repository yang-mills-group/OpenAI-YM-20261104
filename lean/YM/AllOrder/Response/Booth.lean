import YM.AllOrder.Response.Stream
import YM.X.Gauss.Expect
/-!
# Positive-definite *actual* Hessian supplies normalized covariance expectations
From Treaty certificate. Independent of external pin, preserves exact numerator conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
open GaussianScore
variable {Y X:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y][BorelSpace Y]{V:X×Y→ℝ}{ρ:X→Y}{A H:ℝ×(X×Y)→ℝ}(h:Treaty V ρ A H)
local notation "F"=> fderiv ℝ ρ 0
local notation "Ω"=> X×Y
section castle
noncomputable def castle (V:X×Y →ℝ)(ρ:X→Y)(h:Steered V ρ) : Law Y where
   P:= let L:= fderiv ℝ (fderiv ℝ V) 0; { toFun y:= (L (0,y)).toLinearMap.comp (LinearMap.inr ℝ X Y), map_add' y z:= LinearMap.ext (fun i=> (by change L (0,y+z) (0,i)= L (0,y) (0,i)+_; rw [show ((0:X),y+z)= (0,y)+(0,z) by simp,map_add]; rfl)), map_smul' c y:= LinearMap.ext (fun i=> (by change L (0,c•y) (0,i)= _; rw [show ((0:X),c• y)= c • (0,y) by simp,map_smul]; rfl)) }
   turns x y:= h.hard.isSymmSndFDerivAt le_top|>.eq _ _ -- stuck
   slope:= by
      let f (y:Y):= V (0,y); have he : Laplace.curvature V 0= jet f 2:= by ext1 z; let L:= ContinuousLinearMap.inr ℝ X Y; exact Eq.symm (by unfold Laplace.curvature; change jet (V ∘ L) _ _= _; rw [jet_two_C L.contDiff.contDiffAt h.hard (map_zero _) h.quiet,L.fderiv]; rfl)
      obtain ⟨a,hp,hK⟩:= quadratic_min f fun i hi=> (congr_fun he i) ▸ h.stand i hi
      refine ⟨a,hp,fun i=>?_⟩; apply (hK i).trans; rw [←he]; unfold Laplace.curvature; rw [jet_two_H]; exact le_of_eq (by change (2:ℝ)⁻¹ * fderiv ℝ (fderiv ℝ V) 0 (0,i) (0,i)= fderiv ℝ (fderiv ℝ V) 0 (0,i) (0,i)/2; ring)
   smooth:= by let L:= fderiv ℝ (fderiv ℝ V) 0; change Continuous (fun y:Y=> L (0,y) (0,y)); fun_prop
variable (Γ:Law Y)(μ:Measure Y)[μ.IsAddHaarMeasure]
noncomputable def capital (Γ:Law Y) (μ:Measure Y):= ∫ y,Γ.kern y ∂μ
lemma capital_pos : 0< capital Γ μ:= by have hi:= Γ.integrable_entry (A:=1) μ (Zone.Invoice.const (1:ℝ)) continuous_const; rw [one_mul] at hi; exact integral_exp_pos hi
end castle
end YM.AllOrder.Response
