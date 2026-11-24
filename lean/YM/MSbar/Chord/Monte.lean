/- The termwise derivative induction in will uses the zero- and successor-order
curry maps, as in `iteratedFDeriv_tsum`.
Upstream source: Mathlib/Analysis/Calculus/SmoothSeries.lean
Authors: Sébastien Gouëzel. Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.MSbar.Chord.Fig
import Mathlib.Analysis.Calculus.SmoothSeries
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open AnalyticBridge.SectorAffine.Offset Set
open scoped Topology Classical BigOperators ContDiff
variable {E F:Type} {A:Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F] {f:A→E→F}{y:E}{n:ℕ}{k:A→ℝ}{U:Set E}
variable (h:IsOpen U)(hU:Convex ℝ U)(hf:∀ i x,x∈U → Through n (f i) x (k i)) (hp:Summable k)
local notation "H"=> fun x=>∑' i,f i x
local notation "J"=> iteratedFDeriv ℝ
local notation "∆"=> fderiv ℝ
include h hU hf hp
lemma will {j:ℕ}(hL:j≤n)(y:E)(hy:y∈ U): HasSum (fun i=> J j (f i) y) (J j H y):=by
    induction j generalizing y with
    | zero=>
       have ht(i): ‖f i y‖ ≤ k i:= norm_iteratedFDeriv_zero (𝕜:=ℝ)|>.symm.trans_le ((hf i y hy).pay 0 (Nat.zero_le _)); have he:= (Summable.of_norm_bounded hp ht).hasSum
       simp_rw [iteratedFDeriv_zero_eq_comp]; exact (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum he -- syntax
    | succ t ih=>
       let G(i):= J t (f i); have hA:G=G:=rfl; let g(x):=∑' i,G i x; have ht(i x)(hk:x∈U):HasFDerivAt (G i) (∆ (G i) x) x:= ((hf i _ hk).smooth.differentiableAt_iteratedFDeriv (show (t:WithTop ℕ∞)< (n:WithTop ℕ∞) from Nat.cast_lt.mpr (by omega))).hasFDerivAt
       have Hv(i x)(hk:x∈U): ‖∆ (G i) x‖ ≤ k i:= by have he:= (hf i _ hk).pay _ hL; rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.norm_map] at he; exact he
       have hz:=hasFDerivAt_tsum_of_isPreconnected hp h hU.isPreconnected ht Hv hy (ih (by omega) _ hy|>.summable) hy; have hv: g=ᶠ[𝓝 y] J t H:= (show ∀ᶠ x in 𝓝 y,x∈U from h.mem_nhds hy).mono (fun x hi=> (ih (by omega) x hi).tsum_eq); have hR := (hz.congr_of_eventuallyEq hv.symm).fderiv
       simp_rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]; rw [hR]; exact ((continuousMultilinearCurryLeftEquiv ..).symm.toContinuousLinearEquiv.toContinuousLinearMap).hasSum ((Summable.of_norm_bounded hp (fun i=> Hv i y hy)).hasSum)
lemma topS (x:E)(hx:x∈U) : Through n (fun x=> ∑' i,f i x) x (∑' i,k i):=by
   let F:= (fun x=>∑' i,f i x); have hr(j:ℕ)(hm:j≤n)(x:E)(hx:x∈U): J j F x=∑' i,J j (f i) x:= (will h hU hf hp hm x hx).tsum_eq.symm
   have hh:ContDiffOn ℝ n F U:=by
       refine (contDiffOn_iff_continuousOn_differentiableOn h.uniqueDiffOn).mpr ⟨fun j hj=>?_,fun j hj=>?_⟩
       · have hv(j)(hk:j≤n): ContinuousOn (J j F) U:=by
             let g(i):= J j (f i)
             have Hv:= tendstoUniformlyOn_tsum hp (fun i x hx=> (hf i x hx).pay j hk); apply ContinuousOn.congr (f:=fun x=>∑' i,g i x) (TendstoUniformlyOn.continuousOn Hv (Eventually.frequently (Eventually.of_forall (fun I=>?_)))) (fun _ hx=> hr _ hk _ hx)
             exact continuousOn_finsetSum _ (fun i _ y hy=>((hf i y hy).smooth.continuousAt_iteratedFDeriv (by exact_mod_cast hk)).continuousWithinAt)
         exact (hv j (by exact_mod_cast hj)).congr (iteratedFDerivWithin_of_isOpen j h)
       apply DifferentiableOn.congr (f:=J j F) _ (iteratedFDerivWithin_of_isOpen j h)
       have hv : j<n:=by exact_mod_cast hj
       intro x hx; let G(i):= J j (f i); have ht(i x)(hk:x∈U):HasFDerivAt (G i) (∆ (G i) x) x:= ((hf i _ hk).smooth.differentiableAt_iteratedFDeriv (show (j:WithTop ℕ∞)< (n:WithTop ℕ∞) from Nat.cast_lt.mpr hv)).hasFDerivAt
       have hZ(i x)(hk:x∈U):‖∆ (G i) x‖ ≤ k i:=by have he:= (hf i _ hk).pay (j+1) hv; rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply,LinearIsometryEquiv.norm_map] at he; exact he
       have hp:= hasFDerivAt_tsum_of_isPreconnected hp h hU.isPreconnected ht hZ hx (will h hU hf hp hv.le x hx|>.summable) hx; apply DifferentiableAt.differentiableWithinAt; exact (hp.congr_of_eventuallyEq ((show ∀ᶠ y in 𝓝 x,y∈U from h.mem_nhds hx).mono fun i hk=> hr j hv.le i hk)).differentiableAt
   refine ⟨(hh x hx).contDiffAt (h.mem_nhds hx),fun j hk=>?_⟩; rw [show J j _ _=_ from hr j hk x hx]; let v:= fun i=> J j (f i) x; have hv:=hp.of_nonneg_of_le (fun i=>norm_nonneg (v i)) (fun i=> (hf i x hx).pay j hk); exact (norm_tsum_le_tsum_norm hv).trans (hv.tsum_le_tsum (fun i=> (hf i x hx).pay j hk) hp)
end YM.MSbar.Midpoint
