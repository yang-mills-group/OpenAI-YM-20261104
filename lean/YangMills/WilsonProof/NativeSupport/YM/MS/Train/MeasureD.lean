import YM.MS.Train.MeasureD
import YM.MS.Pearl.Ivy
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
/-!
# Normalization

Wick: dimensions are `z=-ε` here. variables tested at every full auxiliary axis (arbitrary high integer `E=Fin(4+2*m)`), preserving active four axes. We use an exponent weighting
 of log dimension $Γ$ argument, with all scale factors shared by momentum loops (not coupling). Chosen $ν = μ e^{γ_E/2}/√(4π)$ as in manuscript; y = log ν. Γ defined independently.
 In particular the eventual limit $ε→0$ won't scale away finite parts. Default `Full Sturdy` for unmarked. Uses Earth density factor $Γ(z+1)/π^z$ removed
 by `Arc`, so restore via exponential here.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Train
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{Z:ℂ}{a:ℝ}{m n h:ℕ}
lemma room_pos : 0<room:= by unfold room; positivity
@[simp] lemma feeD_zero : feeD 0=room:=by simp [feeD,Complex.Gamma_one]
lemma fee_non (z:ℂ)(hz:z∈Town): (z+1).re>0:= by change 0<2*z.re+1 at hz; rw [Complex.add_re,Complex.one_re]; linarith
lemma fee_H : Forest Town feeD:= by
   intro z hz; obtain ht:= Complex.Gamma_ne_zero_of_re_pos (fee_non z hz); obtain hx : DifferentiableAt ℂ Complex.Gamma (z+1):= by refine Complex.differentiableAt_Gamma _ (fun m hm=>?_); obtain ht:= fee_non z hz; rw [hm] at ht; simp at ht; linarith [Nat.cast_nonneg (α:=ℝ) m]
   unfold feeD; refine ( show DifferentiableAt ℂ (fun z:ℂ=>(room:ℂ)* Complex.exp (z*((Real.log π-2*Real.log (2*π):ℝ):ℂ))) z from by fun_prop).div (hx.comp z ( f:=fun z:ℂ=>z+1) ( by fun_prop)) ht
lemma fee_real (x:ℂ)(h:star x=x): star (feeD x)=feeD x:= by simp [feeD,← Complex.Gamma_conj, ← Complex.exp_conj,show starRingEnd ℂ x=x from h]; rw [map_ofNat]
lemma fee_n (z:ℂ)(hz:z∈Town): feeD z≠0:= div_ne_zero (mul_ne_zero (by exact_mod_cast room_pos.ne') (Complex.exp_ne_zero _)) (Complex.Gamma_ne_zero_of_re_pos (fee_non z hz))
lemma fee_T (y:ℝ): ∃ R:ℝ, 0<R∧Forest (disc R) (fun z=> tenorK z y):= by obtain ⟨R,hR,hV⟩:= Metric.mem_nhds_iff.mp (way.mem_nhds (show (0:ℂ)∈Town by simpa using Town_nat 0)); refine ⟨R,hR,fun i hi=>?_⟩; unfold tenorK; simp_rw [cubic]; exact ( DifferentiableAt.mul (by fun_prop) (fee_H i (hV hi))) -- patch
lemma fee_T0 (y:ℝ) : tenorK 0 y=room:= by simp [tenorK,Pearl.weight,toll,amount]
lemma restore_tape (y:ℝ) (z:ℂ): tenorK z y=feeD z * Complex.exp ( -(y:ℂ)*2*z):= by unfold tenorK; rw [cubic]; simp_rw [gNat]; push_cast; ring_nf
end YM.MS.Train
