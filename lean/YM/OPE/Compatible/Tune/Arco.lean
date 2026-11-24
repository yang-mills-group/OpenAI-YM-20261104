import YM.OPE.Compatible.Tune.Pur
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M:Type}{d k:ℕ}{r p μ:ℝ}{V:ℕ→ ΦB (Dryst d)}{T:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)}
open scoped RealInnerProductSpace
local notation "J!"=> Dryst d
local notation "W!"=> Jewel (Dryst d)
local notation "τ!"=>τΓ (Dryst d)
local notation "U!"=>τ₀ (Dryst d)
variable (H: Auth V T μ)
include H
-- Cost. real ν
lemma Auth.breeze (v:W!): let g:=V 0; g 1 v v=2*⟪v 0,v 1⟫:=by
       intro g; let p:= U! (v 0); let q:=U! (v 1); let r:=U! (v 2); change V 0 1 v v=_; have hh(a): V 0 1 (τ! a) (τ! a)=0:=by rw[(H.gauge.drum.one ..).1,(H.gauge.drum.nil ..).2]
       calc
          _= g 1 (p+τ! q+τ! (τ! r)) (p+τ! q+τ! (τ! r)):= by rw [show p+τ! q+τ! (τ! r)=v from τwrite _]
          _ = _:=by
             dsimp only[g]; simp only[map_add,LinearMap.add_apply,(H.gauge.drum.one ..).1,(H.gauge.drum.one ..).2,(H.gauge.drum.nil ..).1,(H.gauge.drum.nil ..).2]; unfold p q; simp only [H.tilt,zero_add,add_zero,H.core,τat]; rw [real_inner_comm (v 1) (v 0)]; ring -- hh unused
lemma Auth.breath (v:W!): V 0 2 v v=2*⟪v 0,v 2⟫+‖v 1‖^2+ V 0 2 (U! (v 0)) (U! (v 0)):=by
       let p:= U! (v 0); let q:=U! (v 1); let r:=U! (v 2); calc
          _= V 0 2 (p+τ! q+τ! (τ! r)) (p+τ! q+τ! (τ! r)):= by rw [show p+τ! q+τ! (τ! r)=v from τwrite _]
          _ = _:=by
             simp only[map_add,LinearMap.add_apply,(H.gauge.drum.two ..).1,(H.gauge.drum.two ..).2,(H.gauge.drum.one ..).1,(H.gauge.drum.one ..).2,(H.gauge.drum.nil ..).2]; unfold p q r; simp only[H.tilt,H.core,τat,zero_add,add_zero]; rw [real_inner_comm (v 2) (v 0),real_inner_self_eq_norm_sq];ring
structure Clamp (p:ℕ)(μ:ℝ)(F:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d))(V:ℕ→ ΦB (Dryst d)): Prop where
      x0 (x:Dryst d):F (τ₀ (Dryst d) x) 0= (μ^p) • x
      pair (x:Dryst d)(t:Fin 3): V 0 t (F (τ₀ (Dryst d) x)) (F (τ₀ (Dryst d) x))= V p t (τ₀ (Dryst d) x) (τ₀ (Dryst d) x)
variable {Y:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)}(Q:Clamp k μ Y V)
include Q
lemma Clamp.crispAct (x:J!) :inner ℝ ((μ^k) • x) (Y (τ₀ (Dryst d) x) 1)=0:=by
       let a:=U! x; let v:=Y a; have ht := H.breeze v; change V 0 1 (Y a) (Y a)=2*inner ℝ (Y a 0) (Y a 1) at ht; rw [show _=V k 1 a a from Q.pair x 1, chargeOne H.gauge, show V 0 1 a a=0 from H.tilt x x,mul_zero,show Y a 0=_ from Q.x0 x] at ht; change inner ℝ ((μ^k) • x) (Y a 1)=0; linarith
noncomputable def SurTax (T:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d))(V:ℕ→ ΦB (Dryst d))(μ:ℝ): Artπ (Dryst d):= (μ^2)⁻¹ • originω (partPay (μ:=μ) (V:=V) (U:=T))
lemma Clamp.bold (x:J!)(hp:0< μ):
    let a:=Y (τ₀ (Dryst d) x); 2*⟪(μ^k) • x, a 2⟫ + ‖a 1‖^2 = (k:ℝ) * (μ^k)^2 * SurTax T V μ x x:=by
       intro a; have hh:= H.breath a; have ht':a 0= (μ^k) • x:= Q.x0 x; rw[ht', show V 0 2 a a= _ from Q.pair x 2,bubbleC H.gauge _ _ hp.ne',map_smul,map_smul,map_smul,LinearMap.smul_apply,smul_eq_mul,smul_eq_mul] at hh; rw [show SurTax T V μ x x=(μ^2)⁻¹*partPay (μ:=μ) (V:=V) (U:=T) (U! x) (U! x) from rfl]; rw [div_eq_mul_inv] at hh; linarith only [hh] -- powers undone
end YM.OPE.Hark
