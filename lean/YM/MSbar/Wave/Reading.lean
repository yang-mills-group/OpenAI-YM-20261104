import YM.MSbar.Wave.Warm
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open Gauge Lattice Wilson RG Tree Precision Exterior Push Push.Uniform
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open Set MvPolynomial Native.Chart
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "X"=> Positions (Primary n G)
local notation "V"=> fieldDir G n 1
local notation "α"=> ((0:ℝ),(1:ℝ))
variable (s:Site n→G.Color)(R:PathData G)(p:Clip)(F:Nesting G n)(q:ℕ)
local notation "ϑ"=> tariff n q p R F
variable (x:Positions (Primary n G)){S:ℝ → Config G n→ℝ}(h:Trend S F R p q)
local notation "j!"=> checkK s p R F q x
def impulse (n:Side)(G:Gauge)(p:Cacao.Pot (Primary n G))(x: Positions (Primary n G)):= fderiv ℝ (fun y:Positions (Primary n G)=>MvPolynomial.eval y p) x
noncomputable def warp (t:ℝ):=∑ i∈ Finset.range (q+1),t^i*impulse n G (µ i (tariff n q p R F)) x (speedsK s (t•x))
include h
lemma serveP : ∀ᶠ t:ℝ in Γ,pine (checkK s p R F q x) 1 (t,0) (0,1) = t^2*warp s R p F q x t:=by
    let P:=ϑ; let D:=j!; let Q(g:ℝ):=g•x; have he:Tendsto Q (𝓝 0) (𝓝 0):=by simpa only [show Q 0=0 from zero_smul ..] using (show Continuous Q from by unfold Q; fun_prop).tendsto 0
    have hx: Tendsto (fun u:ℝ=>(u,(0:ℝ))) Γ (𝓝 0):=(continuousAt_id.prodMk continuousAt_const).mono_left nhdsWithin_le_nhds
    filter_upwards [width, hx.eventually ((checkD s p R F q h x).eventually (by simp)),(he.mono_left nhdsWithin_le_nhds).eventually (spruceT s)] with t ht hD hg
    let A(z:ℝ):= t⁻¹ • cones s (t • (z,x)); let u:=speedsK s (t•x); have hv : t≠0:=ht.1.ne'
    have hG : t*(0:ℝ)=0:=mul_zero _
    have hz(v): t • (v,x)=(t*v,Q t):=rfl
    have ha:A 0=x:=by unfold A; rw [hz,hG,hg.1]; exact inv_smul_smul₀ hv _
    have hh:HasDerivAt A u 0:=by
       let v(z:ℝ):= t*z; have hw : HasDerivAt v t 0:=by simpa using! (hasDerivAt_id' 0|>.const_mul t)
       let F₀(z:ℝ):= cones s (z,t•x); have hz':HasDerivAt F₀ u (v 0):=by rw [show v 0=0 from hG]; exact hg.2
       have hh:= (hz'.scomp 0 hw).const_smul t⁻¹; rwa [inv_smul_smul₀ hv u] at hh
    let F₀(z:ℝ):= D (t,z); let H₀(v:X):= taste q (picture v P) t
    have hs : F₀ = fun z => t^2*H₀ (A z)-scaledT q P (t,t•x):=funext fun z=>by unfold H₀ F₀ D checkK; rw [← scale_r q P (cool n q p R F h.plane)] ; unfold A; rw [ smul_inv_smul₀ hv]; -- transparency
    have hp : HasDerivAt (H₀ ∘ A) (warp s R p F q x t) 0 := by
       let f(i:ℕ)(v: X):= MvPolynomial.eval v (µ i P); let a(i:ℕ):= fderiv ℝ (f i) x; have h(i:ℕ):HasFDerivAt (f i) (a i) (A 0):=ha.symm ▸ ((vent (µ i P)).contDiffAt.differentiableAt (by simp)).hasFDerivAt; let g(i:ℕ)(b:ℝ):= t^i*f i (A b); have he(i:ℕ):HasDerivAt (g i) (t^i*a i u) 0:= ((h i).comp_hasDerivAt (0:ℝ) hh).const_mul _
       rw [show H₀ ∘ A = (fun z=>∑ i∈Finset.range (q+1),g i z) from ?_]; swap;· unfold H₀ taste g f picture; simp_rw [PowerSeries.coeff_map];rfl
       exact HasDerivAt.fun_sum fun i _=> he i -- syntax
    let E:=t^2*warp s R p F q x t; have hK : HasDerivAt F₀ E 0:=by rw [hs]; exact (hp.const_mul _).sub_const _
    rw [pineOne]; exact (((show ContDiffAt ℝ ω D (t,0) from hD).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hasDerivAt_const _ t).prodMk (hasDerivAt_id' 0))).unique hK
lemma peel : Grade (warp s R p F q x) (q+1) :=by
    let D(t:ℝ):=pine j! 1 (t,0) (0,1); have ht:D=D:=rfl; have hv : ContDiffAt ℝ ω D 0:=(lyric 1 _ _ _ (checkD s p R F q h x)).comp (f:=fun t:ℝ=>(t,0)) (0:ℝ) (contDiffAt_id.prodMk contDiffAt_const)
    obtain he:= certified hv (q+2); have hc:Grade D (q+1+2):=by
       rw [show q+1+2=q+2+1 from (by omega)]; refine Price.egress he (Eventually.of_forall fun y k hh=>?_); dsimp only; rw [Finset.sum_eq_zero,sub_zero]; exact fun i hp=> by rw [show bill D i=0 from omens s p R F q h x i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)),mul_zero]
    let P:= warp s R p F q x; refine (rollQ 2 (z:=fun t (_:Unit)=>D t) hc).egress ?_
    filter_upwards [width,serveP s R p F q x h] with t ht hh y _; unfold D; rw [hh]; field_simp [ht.1.ne']
-- leading recursion.Values pointwise
noncomputable def flight (A:PowerSeries (Pot (Primary n G))) (i:ℕ) (z:Site n→ G.Color)(x:Positions (Primary n G))(t:ℝ):= impulse n G (µ i A) x (speedsK z (t •x))
omit h
lemma smoothFlight (A:PowerSeries (Pot (Primary n G)))(i:ℕ) : ContDiffAt ℝ ω (flight A i s x) 0:=by
    let g(y:X) := speedsK s y
    have he: ContDiffAt ℝ ω g 0:=by
       let F:= (tint G (Body 1 n)).symm; apply F.contDiff.contDiffAt.comp; refine contDiffAt_pi.mpr fun i=>?_; let L:X→L[ℝ] G.Color:= (ContinuousLinearMap.proj i).comp F.symm.toContinuousLinearMap; exact (show ContDiffAt ℝ ω _ (L 0) from by rw [map_zero]; exact speeds G (ran s i)).comp _ L.contDiff.contDiffAt
    exact (impulse n G (µ i A) x).contDiff.contDiffAt.comp _ ((show ContDiffAt ℝ ω g ((0:ℝ)•x) from zero_smul ℝ x|>.symm ▸ he).comp (f:=fun t:ℝ=>t•x) (0:ℝ) (contDiffAt_id.smul contDiffAt_const))
include h
lemma ascends (p':ℕ)(he:p'≤q): ∑ j∈ Finset.range (p'+1), bill (flight (tariff n q p R F) j s x) (p'-j)=0:=by
    let P:=ϑ; let f(j:ℕ):=flight P j s x; let g(i):=∑ j∈ Finset.range (i+1), bill (f j) (i-j); have hV(t:ℝ) : ∑ i∈ Finset.range (q+1), t^i*g i=∑ i∈Finset.range (q+1),t^i*∑ j∈Finset.range (q-i+1),t^j*bill (f i) j:= by
        let G(i j:ℕ):= t^(i+j)*bill (f i) j; unfold g; have hp(i): t^i*(∑ j∈Finset.range (i+1),bill (f j) (i-j))=∑ j∈Finset.range (i+1),G j (i-j):=by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j hj=>by unfold G; have ht:=Finset.mem_range.mp hj; rw [show j+(i-j)=i by omega])
        simp_rw [hp]; rw [aims]; unfold G; simp_rw [pow_add, mul_assoc, Finset.mul_sum]
    let d(j:ℕ)(t:ℝ):=t^j*(f j t-∑ k∈Finset.range (q-j+1), t^k*bill (f j) k)
    have hG : Grade (fun t=>∑ i∈ Finset.range (q+1),t^i*g i) (q+1):=by
        have hx(j:ℕ)(hk:j≤q): Grade (d j) (q+1):=by
            have hk':q+1=j+(q-j+1):=by omega
            rw [hk']; exact Price.product (q:=q-j+1) (xrise ..) (certified (smoothFlight ..) _) -- check
        let u: Grade (fun t=>∑ i∈ Finset.range (q+1),d i t) (q+1):=Price.bag (Finset.range _) _ (fun i hi=> hx i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        refine (Price.cut (peel s R p F q x h) u).egress (Eventually.of_forall (fun t i _=>?_)); unfold warp; dsimp only; rw [←Finset.sum_sub_distrib,hV]; refine Finset.sum_congr rfl (fun j _=>?_); unfold d; change t^_*f _ t-_=_; ring
    exact magnitude hG p' he
end YM.MSbar.Wave
