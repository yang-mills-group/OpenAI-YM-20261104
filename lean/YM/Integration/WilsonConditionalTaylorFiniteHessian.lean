import YM.Integration.WilsonConditionalTaylorFormalLog
import YM.Integration.WilsonConditionalTaylorSceneCalibration
import YM.FormalBulk08.Broc.Heron

/-! The genuine finite two-leg kinetic functional is twice the real
periodized two-leg kernel of the polynomial (the factor two is 2!). -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorFiniteHessian

open Function Finset MvPolynomial PowerSeries RG Lattice Push.Uniform Precision
open MSbar MSbar.Midpoint MSbar.Wave MSbar.Cacao FormalBulk08 FormalBulk08.Broc
open FormalBulk08.Lava FormalBulk08.Jets FormalBulk08.Series
open AnalyticBridge.VerifiedReset
open PertExtension PertExtension.Series PertExtension.Series.Tested
open WilsonConditionalTaylorFormalLog
open scoped Classical ContDiff BigOperators

variable {I : Type} [Fintype I]

theorem stored (P : MvPolynomial I ℝ) (r : ℕ) :
    PowerSeries.coeff r (paste (fun z=>MvPolynomial.eval z P))=homogeneousComponent r P := by
  apply orbit_ext
  intro x
  let f:=fun z : I→ℝ=>MvPolynomial.eval z P
  let L:=ContinuousLinearMap.toSpanSingleton ℝ x
  let A:=PowerSeries.mk (fun d=>MvPolynomial.eval x (homogeneousComponent d P))
  let M:=max r P.totalDegree
  have eqn : f ∘ L=peval (term A) M := by
    funext t
    change MvPolynomial.eval (t•x) P=∑ d∈range (M+1),t^d*(PowerSeries.coeff d A)
    have expand:=congrArg (MvPolynomial.eval (t•x)) (buys M P (le_max_right ..))
    rw [map_sum] at expand
    rw [←expand]
    exact sum_congr rfl fun d _=>by simp only [A,coeff_mk];exact hene t t x d P
  have hot : ContDiffAt ℝ ∞ f 0:=(vent P).contDiffAt.of_le le_top
  have line : ContDiffAt ℝ ∞ (f ∘ L) 0:=ContDiffAt.comp (f:=L) 0 (by rw [map_zero]; exact hot) L.contDiff.contDiffAt
  have radial:=FVA2.GermLaplace.jet_pull L f hot 1 r
  have charge:=polynomial A M r (le_max_left ..)
  rw [←eqn,quotes _ line] at charge
  rw [trace_paste]
  change Radial.jet f r x=MvPolynomial.eval x (homogeneousComponent r P)
  change Wave.bill (f ∘ L) r=Radial.jet f r (L 1) at radial
  rw [show L 1=x from by simp [L]] at radial
  exact radial.symm.trans ((charge.trans (coeff_mk ..)))

theorem tensor (P : MvPolynomial I ℝ) (r : ℕ) :
    beam (fun z=>MvPolynomial.eval z P) r = marble r P := by
  apply facade_unique (beam_pulse _ ((vent P).contDiffAt.analyticAt) r) (marble_agate r P)
  rw [beam_price,marble_grade,stored]

variable {G : Gauge} {n : Side}

theorem paired (P : Pot (Primary n G)) (u : G.ColorIndex) (a b : Site n) :
    stackP n G P (tuner (Lis.sun G u) a) (tuner (Lis.sun G u) b)=
      2*marble 2 P ![primary (a,(1:Axis)) u, primary (b,(1:Axis)) u] := by
  let q(s : Site n):=primary (s,(1:Axis)) u
  have pick (s : Site n): tuner (Lis.sun G u) s=bolt (q s):=brand (s,(1:Axis)) u
  rw [pick,pick]
  let f:=fun x : Positions (Primary n G)=>MvPolynomial.eval x P
  have h:=congrFun (tensor P 2) ![q a,q b]
  change ((2:ℕ).factorial:ℝ)⁻¹ * iteratedFDeriv ℝ 2 f 0 (dotI ∘ ![q a,q b])=marble 2 P ![q a,q b] at h
  rw [show (dotI ∘ ![q a,q b])=![bolt (q a),bolt (q b)] from by funext i; fin_cases i <;>rfl,
    iteratedFDeriv_two_apply] at h
  change (fderiv ℝ (fderiv ℝ f) 0 (bolt (q a))) (bolt (q b))=2*marble 2 P ![q a,q b]
  norm_num at h
  linarith

theorem moment (P : Pot (Primary n G)) (u : G.ColorIndex) :
    caliper n (Lis.sun G u) P=(Fintype.card (Site n):ℝ)⁻¹ * ∑ a : Site n, ∑ b : Site n,
      (2*marble 2 P ![primary (a,(1:Axis)) u, primary (b,(1:Axis)) u])*coord a b 0^2 := by
  change (Fintype.card (Site n):ℝ)⁻¹ * ∑ a : Site n,∑ b : Site n, stackP n G P (tuner _ a) (tuner _ b)*_ = _
  simp_rw [paired]

end YM.Integration.WilsonConditionalTaylorFiniteHessian
end

