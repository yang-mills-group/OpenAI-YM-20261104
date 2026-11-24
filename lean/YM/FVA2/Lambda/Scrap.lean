import YM.FVA2.Lambda.Taken
/-!
# ∫ a petal

 Combining slope via matched general argument. last scalar ∫ da.Solve antiderivative.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.BranchR
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Emit MS.Pearl
open MS.City MS.Plane.Flux
open Area Shells Pages
open Lathe Gaussian
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace ENNReal NNReal
private def W(x:ℝ) := b₀*( (-69*x^3-61*x^2-65*x-13)/(6*(1+x)^5) )
private def K₀(x:ℝ):= b₀*( 3*(-3*x-1)/(4*(1+x)^3) )
variable {x:ℝ}(hx:0≤x)
include hx
lemma derivative_w : HasDerivAt W (petal x) x:= by
    unfold W; let h:= hasDerivAt_id' x
    convert! (( ( ( ((h.pow 3).const_mul (-69)|>.fun_sub ((h.pow 2).const_mul 61)).fun_sub (h.const_mul 65)|>.sub_const 13 ).div ( (( h.const_add 1 ).pow 5).const_mul 6 ) (by dsimp; positivity) ).const_mul b₀ )) using 1; unfold petal; norm_num; field_simp; ring -- inspect syntax
lemma derivative_c : HasDerivAt K₀ (petalC x) x:= by
    let h:= hasDerivAt_id' x; unfold K₀; convert! ((( ((h.const_mul (-3)).sub_const 1).const_mul 3 ).div ((( h.const_add 1 ).pow 3).const_mul 4 ) ( by dsimp; positivity ) )|>.const_mul b₀ ) using 1; unfold petalC; norm_num; field_simp; ring
omit hx
lemma torsion (F D:ℝ→ℝ)(h:∀ x,0≤x → HasDerivAt F ( D x ) x )(ht:ContinuousOn D ( Set.Ici 0 )) : (∫ a,D a∂unitμ)= F 1-F 0:= by
    let K:= Set.uIcc (0:ℝ) 1; have hp: K ⊆ Set.Ici 0:= by unfold K; rw [ Set.uIcc_of_le zero_le_one ]; exact fun i hi=> hi.1
    rw [unitμ,integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1) ]; exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i hi=> h i ( hp hi )) ( (ht.mono hp).intervalIntegrable )
lemma walkW : (∫ q:QP,Absorb jewel q ∂μq)=13/12*b₀:= by
    rw [show (∫ q:QP, Absorb jewel q ∂μq)=(∫ a, petal a∂unitμ) from Try.paid petalQ, torsion W _ (fun _ h=> derivative_w h) ]; · unfold W; ring
    intro x hx; apply ContinuousAt.continuousWithinAt; have hx:0≤x:=hx; unfold petal; fun_prop (disch:=positivity) -- inverse? `with_discharge`
lemma walkC : (∫ q:QP, absorbV q∂μq)= 3/8*b₀:= by
    rw [show (∫ q:QP, absorbV q∂μq)=(∫ a, petalC a∂unitμ) from Try.paid petalCQ, torsion K₀ _ (fun _ h=> derivative_c h) ]; · unfold K₀; ring
    intro x hx; apply ContinuousAt.continuousWithinAt; have hx:0≤x:=hx; unfold petalC; fun_prop (disch:=positivity)
end YM.FVA2.Lambda.BranchR
