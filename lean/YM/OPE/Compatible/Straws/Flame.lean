import YM.OPE.Compatible.Straws.Mine
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded
variable (F:Fiber E G I)(X:Path E G D)(u: Keys G D)
abbrev Path.timber (t:ℝ):E:= t⁻¹ • X.A (t•u)
omit [BorelSpace E] in
lemma Timber : Gael (X.timber u):= Gael.walk (fun t=>X.A (t•u)) ((show ContDiffAt ℝ ∞ X.A ((0:ℝ) • u) from by rw [zero_smul]; exact X.hA).comp 0 (contDiffAt_id.smul contDiffAt_const)) (by rw [zero_smul,X.ha])
omit [FiniteDimensional ℝ E][BorelSpace E] in
lemma stander : Tendsto (X.timber u) Lf (𝓝 (X.deck u)):=by
      have ht:= ((X.hA.differentiableAt (by simp)).hasFDerivAt.hasLineDerivAt u).tendsto_slope_zero; simp only [zero_add,X.ha,sub_zero] at ht; exact ht.mono_left (nhdsWithin_mono _ (by simp))
def δAre (t:ℝ):= F.M (X.timber u t)-F.M (X.deck u)
omit [BorelSpace E] in
lemma candle : ∃ a b,Reads (δAre F X u) ⟨0,a,b⟩:=by
     have hx:= Gael.oath (Timber X u); have hp: Gael (δAre F X u):= Exists.intro _ ((Reads.tours F.M hx).minus (Reads.constants (F.M (X.deck u))))
     obtain ⟨⟨a,b,c⟩,hc⟩:=hp; refine ⟨b,c,?_⟩; rw [← show a=0 from ?_]; exact hc; apply tendsto_nhds_unique hc.limit; convert! (F.M.continuous.continuousAt.tendsto.comp (stander X u)).sub (tendsto_const_nhds (x:= F.M (X.deck u))) using 2; simp
variable {F X}{p: Keys G D→ℝ}(Z:F.SeriesUp X p) {P:ChartRatio G}(R:LocalRatio P)
namespace SeriesUp
-- extra free coordinate carrier (density and Haar factor)
local notation "y0"=> δAre F X u
local notation "W"=> cloth F P
def horsa (u:Keys G D)(t:ℝ)(P:ChartRatio G):ℝ:=
     (Chart.jacobian P (0:U!))⁻¹ * Chart.jacobian P (t • u) * Real.exp (-(p (t • u))/t^2 + Z.Z.P u u/2- F.u_q (X.timber u t))
include R
omit [BorelSpace E] in
lemma horsB : Gael fun t=> Z.horsa u t P:=by
     let g(t:ℝ):= Chart.jacobian P (t • u); let d:=Chart.jacobian P (0:U!); have hx:= (Pawn.calm ((Chart.Ratio.jacobian_smooth R).of_le le_top)).stale u; let Q: E→L[ℝ] (E×Y!):= (ContinuousLinearMap.id ℝ E).prod F.M; have hp:Bond F.u_q:= ((Pawn.trio F.H).toll 0).compLinear Q.toLinearMap; have ht:= Gael.oath (Gael.climb _ hp (Timber X u)); let v:=Z.Z.P u u/2
     let w(t:ℝ):= -(p (t • u))/t^2+v-F.u_q (X.timber u t); have hh:= ((((Pawn.trio Z.pu).stale u).neg.sum (Reads.constants v)).minus ht).roofer; refine Exists.intro _ (((Reads.constants d⁻¹).pile hx).pile hh |>.cong ?_); filter_upwards with i; change _ * Real.exp _ = _* Real.exp ((-(p (i•u) /_)+_)-_); unfold u_q -- try
     rw [neg_div];rfl
omit Z R [BorelSpace E] in
lemma fieldP (u:U!)(y:Y!)(t:ℝ)(ht:0<t):
     t⁻¹ • Spine (I:=I) X (t • camp F X (u,y))= drape E Y! F.M (X.timber u t,y-δAre F X u t):=by
            unfold Spine; rw [map_smul,map_smul,(rig F X (u,y)).1,(rig F X (u,y)).2]; erw [Prod.smul_mk,inv_smul_smul₀ ht.ne']; apply Prod.ext; rfl; change _+y=F.M _+(y-(F.M _-_)); abel
omit [BorelSpace E] in
lemma campH (a b:Y!)(h:Reads (δAre F X u) ⟨0,a,b⟩)(y:Y!):
     let Y:= Warp F.Q a b
     Z.C.hat P (camp F X (u,y))=trill (fun t=> Z.horsa u t P)*Y y* usher (δAre F X u) (X.timber u) W y :=by
          intro Y
          let β:= camp F X (u,y); let k:=δAre F X u; let v(t:ℝ):E×Y!:=drape E Y! F.M (X.timber u t,y-k t)
          have hl:Gael v:=by let w:Gael (fun t=>(X.timber u t,y-k t)):= Gael.union (Timber X u) ⟨_,(Reads.constants _).minus h⟩; exact Gael.up w (drape E Y! F.M).toContinuousLinearMap
          have hv:= Gael.oath (horsB u Z R); let C:= Warp F.Q a b y; let α(t:ℝ):= F.Q.P y (k t)-F.Q.P (k t) (k t)/2
          have hw: Reads (fun t=>Real.exp (α t)) C:=warpR F.Q _ _ _ _ h
          have he:= cooking F.H (signB F R) hl; apply (Waterfall Z.C β R).equality; apply ((hv.pile hw).pile he).cong
          filter_upwards [Tested.eventually_pos] with t (ht:0<t)
          have ha : Spine (I:=I) X (t • β)=t • v t:=by rw [show v t= _ from (fieldP u y t ht).symm, smul_inv_smul₀ ht.ne']
          have hh: BR (t • β)= (t • v t).2:=by rw [← ha];rfl
          have hV: BL (t • β)= t • u:=by rw [map_smul,(rig F X (u,y)).1]
          let w:=wSign F P; let U(y:U!):=Chart.jacobian P y; have hW: warmer P Z.C.w (t • β)= U (t • u)*w (t • v t):=by unfold warmer w wSign; rw [Z.v]; simp only [Pi.mul_apply]; rw [show Chart.jacobian P (t • β)=_ from jacSplit (Equiv.refl (D ⊕ I)) _ _,hh,hV,Function.comp_apply,ha]; unfold U; ring -- check syntax
          have hz: warmer P Z.C.w 0=U 0*w 0:=by unfold warmer w wSign; rw [Z.v]; simp only [Pi.mul_apply,_root_.Function.comp_apply,SpineBlew]; rw [jacSplit (Equiv.refl (D ⊕ I)),map_zero,map_zero]; unfold U; rw [Prod.snd_zero]; ring
          have hj:=Z.hX u y; change jet Z.C.f 2 β= _ at hj; have hy: Z.C.f (t • β)= F.f (t • v t)+p (t • u):=by rw [Z.f]; simp only [Pi.add_apply,Function.comp_apply,hV,ha]
          have hk: jet F.f 2 (v t)= F.u_q (X.timber u t)+F.Q.P (y-k t) (y-k t)/2:=F.split ..
          change (warmer P Z.C.w 0)⁻¹ * (warmer P Z.C.w (t • β)*Real.exp (higher Z.C.f t β))= (Z.horsa u t P)*Real.exp (α t)*((w 0)⁻¹*(w (t • v t)*Real.exp (higher F.f t (v t)))); unfold horsa; rw [hW,hz]; unfold higher; rw [hj,hk,hy]; change _= ((_ * U (t • u))*Real.exp _*Real.exp (α t)) * (_*(w (t • v t)*_))
          rw [mul_inv_rev, mul_assoc (_*U _), ← Real.exp_add]
          let l:= -(p (t • u))/t^2 + Z.Z.P u u/2- F.u_q (X.timber u t)+α t; let q:= -(F.f (t • v t))/t^2+ (F.u_q (X.timber u t)+F.Q.P (y-k t) (y-k t)/2)
          rw [show -(F.f (t • v t)+p (t • u))/t^2+ (Z.Z.P u u/2+F.Q.P y y/2)=l+q from ?_,Real.exp_add]; unfold q l w U; ring
          unfold l q α; simp only [map_sub,LinearMap.sub_apply]; rw [F.Q.turns (k t) y];ring
end SeriesUp
end Fiber
end YM.OPE.Libra
