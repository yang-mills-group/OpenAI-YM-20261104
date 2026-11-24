import YM.X.Stems.Log
/-!
# The order-one unnormalized positive-face V3 with all neighbor links in native normalization.
Uses physical chord normalization. Cook ⇒ known factor in plaquette curl and compatibility with one Ward variation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems.Log
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Gauge Source ProjectorNext.Calibration Gauss Jet PertExtension.Series.Tested Work.F03
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Pointwise
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {x y : ℝ → G.El} {z : ℝ → G.Color}{i:ℕ}
local notation "X"=> G.mat
local notation "A"=> G.colorMat

def cost : G.Color→ℝ:= G.price ∘ G.lieExp
lemma cost_nice {G:Gauge} : ContDiffAt ℝ ω (cost (G:=G)) 0:= price_smooth G.exp_jet.contDiffAt
lemma cost_even (k:ℕ)(h:Odd k)(v:G.Color): jet cost k v=0:= by
   rw [homogeneous_derivative _ _ _ (cost_nice.of_le le_top)]
   let p : ℝ→ℝ:=fun r=>cost (r • v)
   have hf : (fun t=>p (-t))=p:=by ext t; unfold p cost; simp [Work.F03.exp_neg_color]
   have hp : iteratedDeriv k p 0=0 := by
      have he:= iteratedDeriv_comp_neg k p 0; rw [hf,h.neg_pow] at he; simp only [one_pow, smul_eq_mul,one_mul,neg_zero,neg_mul] at he; linarith
   rw [hp,mul_zero] -- edit
lemma cost_zero {G:Gauge}{j:ℕ}(h:j<2): jet (cost (G:=G)) j=0:=by
   interval_cases j<;> funext v
   · simp [cost,Gauge.mat_lieExp_zero]
   exact cost_even 1 odd_one v
lemma cost_two (v:G.Color): jet cost 2 v= ‖v‖^2/2:= by
   have H:= Roots.Exponent v
   have ha: Tendsto (fun t:ℝ=> (t⁻¹)^2 * cost (t•v)) (𝓝[>] 0) (𝓝 (jet cost 2 v)):= ((directions (cost_nice.of_le le_top) v).shift (fun i hi=> congr_fun (cost_zero hi) v)).tendsto_first
   have he : Tendsto (fun t : ℝ=> cost (t•v)/t^2) (𝓝[≠] 0) (𝓝 (‖v‖^2/2)) := price_limit H.lights H.matL
   apply tendsto_nhds_unique ha; refine (he.mono_left (nhdsGT_le_nhdsNE 0)).congr ?_; intro a; rw [div_eq_mul_inv, inv_pow]; ring
lemma turns (u v : G.Color): fderiv ℝ (jet cost 2) u v= Inner.inner ℝ u v:= by
   rw [funext (cost_two (G:=G))]; let i:=Inner.inner ℝ u v
   let f (x : G.Color):= ‖x‖^2/ (2:ℝ);
   let L:= innerSL ℝ u; have he:fderiv ℝ f u=(2:ℝ)⁻¹ • (2 • L):= by
      have ht : f=(2:ℝ)⁻¹ • (fun x:G.Color=>‖x‖^2):= funext fun x=> (by unfold f; dsimp only [Pi.smul_apply,smul_eq_mul];ring); rw [ht]; exact ((hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_smul (2:ℝ)⁻¹).fderiv
   rw [he]; simp [two_smul,L]; ring

variable {a p:G.Color}
namespace Roots
variable (h:Roots x a p)
include h
lemma frame (hi:i≤3): someJ (G.price ∘ x) i= if i=2 then ‖a‖^2/2 else if i=3 then Inner.inner ℝ a p else 0:= by
   let f:=record x
   have he:= tick_base (p:=cost) (n:=2) cost_nice (show Act 4 f (someJ f) from ⟨h.ok,fun _ _=> rfl⟩) (by simp [f,h.zero]) (fun i hi=> cost_zero hi) hi -- inspect
   have ht : someJ (cost ∘ f) i=someJ (G.price ∘ x) i:= by rw [someJ, someJ]; exact congr_arg _ ( (show cost ∘ f =ᶠ[𝓝 0] G.price ∘ x from h.reverse.mono (fun _ ht=> congr_arg G.price ht)).iteratedDeriv_eq i)
   rw [←ht,he,show someJ f 1=a from h.someL,show someJ f 2=p from h.someP,cost_two,cost_even 3 (by decide),turns,zero_add] -- rw cost even argument
end Roots

def sub (a b c d:G.Color):= shift a b + shift (a+b) (-c) + shift (a+b-c) (-d)
def fire (v:Brush G)(x: Cover)(i j:Axis):= sub (v (x,i)) (v (x+step i,j)) (v (x+step j,i)) (v (x,j))
def flame (p:Face ℤ)(U:CoverConfig G):= G.price (faceValue U p)
lemma fixture (p:Face ℤ)(v:Brush G): Roots (fun r:ℝ=> faceValue (posit (r • v)) p) (curl v p.1 p.2.val.1 p.2.val.2) (fire v p.1 p.2.val.1 p.2.val.2):= by
   rcases p with ⟨x,⟨i,j⟩,he⟩; let a:=v (x,i);let b:=v (x+step i,j);let c := v (x+step j,i);let d:=v (x,j)
   have h (t:G.Color)(r:ℝ): (G.lieExp (r • t))⁻¹=G.lieExp (r • (-t)):= by rw [smul_neg,exp_neg_color]
   have hb : (fun r:ℝ=> faceValue (posit (r • v)) (x,⟨(i,j),he⟩)) = ((((fun r:ℝ=> G.lieExp (r • a)) * (fun r=> G.lieExp (r • b)))*(fun r=> G.lieExp (r • (-c))))* (fun r=> G.lieExp (r • (-d)))):= by funext r; unfold faceValue; rw [Pert.Bare.square_links]; simp only [posit,Pi.smul_apply, Pi.mul_apply,h]; rfl
   have H:= (((Roots.Exponent a).times (Roots.Exponent b)).times (Roots.Exponent (-c))).times (Roots.Exponent (-d))
   change Roots _ (curl v x i j) (sub a b c d)
   rw [hb]; simp only [zero_add,add_zero] at H
   convert H using 1
   · unfold curl; unfold a b c d; abel
   unfold sub; congr 2 <;> abel
lemma brief (p:Face ℤ): Small G (flame (G:=G) p):= by
   have he (u:G.El):G.price u=‖X u -1‖^2/ G.colorScale^2/2:= by rw [←div_pow]; change _=G.chord u^2/2; rw [G.chord_price];ring
   change Small G (fun U=> G.price (faceValue U p)); simp_rw [he]
   exact (Small.path (G:=G) _ _).comp ((((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _).div_const _)
lemma flame_root (p:Face ℤ) (v:Brush G) {i:ℕ}(hi:i≤3): someJ (along (flame p) v) i= if i=2 then ‖curl v p.1 p.2.val.1 p.2.val.2‖^2/2 else if i=3 then Inner.inner ℝ (curl v p.1 p.2.val.1 p.2.val.2) (fire v p.1 p.2.val.1 p.2.val.2) else 0 := (fixture p v).frame hi
end YM.PositionX.Stems.Log
