import YM.MSbar.Tilt.Wade
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tilt
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua Bout
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "K"=>Positions (Primary n G)
local notation "V"=> G.Color
variable (z:Site n→G.Color) (x:Positions (Primary n G))
variable {R B C D E t c:ℝ}
noncomputable def reset (z:Site n→G.Color)(t:ℝ)(x:Positions (Primary n G))(s:ℝ) := t⁻¹ • (cones z (s*t,t • x))
noncomputable def regal (z:Site n→G.Color)(x:Positions (Primary n G))(s:ℝ):= x+s • grad z
structure Guide (G:Gauge)(C D:ℝ):Prop where
   r:0<C
   pos: 0 ≤ D
   amount (v:Native.Chart.Rail G × G.Color): ‖v‖<C→ ‖Tilt.wah G v-(v.2+v.1.2-v.1.1)‖≤ D*‖v‖^2 ∧ G.lieExp (Tilt.wah G v)=hit G v.1 1 v.2
lemma gate (G:Gauge):∃ C D,Guide G C D:= by obtain ⟨C,D,hr,hD,h⟩:= prime G; exact ⟨_,_,hr,hD,h⟩
variable (h:Guide G C D)(ht:0<t)(hv:‖tint G _ x‖≤R)(hz:∀ i:Body 1 n, ‖ran z i‖ ≤ R)(hc:t*R<C)
include h ht hv hz hc
local notation "m"=> tint G (Body 1 n)
local notation "α"=> reset z t x
local notation "Z!"=> fun i:Body 1 n=>Native.Chart.head G (ran z i)
lemma firm(s:ℝ)(hs:|s| ≤1) (i:Body 1 n) : let v:= Native.Chart.head G (ran z i) (s*t,t • ((tint G _) x i))
     v=t • ((tint G _) (reset z t x s) i) ∧ G.lieExp v=hit G (ran z i) (s*t) (t • ((tint G _) x i))∧ ‖v-t • ((tint G _) (regal z x s) i)‖≤ D*(t*R)^2 :=by
     intro v; let b:= ran z i; let A:= ((s*t) • b,t • (m x i)); have hR:0 ≤ R:= (norm_nonneg _).trans hv
     have hP : ‖A‖ ≤ t*R:=max_le ((norm_smul ..).trans_le (show _ from (by change |s*t| * _≤ _; rw [abs_mul,abs_of_pos ht]; refine mul_le_mul (mul_le_of_le_one_left ht.le hs) (hz i) (norm_nonneg _) ht.le))) (by rw [norm_smul,Real.norm_of_nonneg ht.le]; exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ i).trans hv) ht.le)
     obtain ⟨h₁,h₂⟩:=h.amount _ (hP.trans_lt hc); change G.lieExp (Tilt.wah G ((s*t) • b,_))= _ at h₂; rw [up] at h₂; change _ ≤ _ at h₁
     refine ⟨?_,?_,?_⟩
     · unfold reset; rw [map_smul, cones, ContinuousLinearEquiv.apply_symm_apply, Pi.smul_apply, smul_inv_smul₀ ht.ne']; unfold v coneT; rw [map_smul];rfl; -- simplifier
     · exact h₂.trans (by unfold A Native.Chart.hit b; simp [smul_neg])
     have hi: tint G _ (grad z) i=b.2-b.1:=by rw [← speedStart, speedsK, ContinuousLinearEquiv.apply_symm_apply]; rw [map_zero]; exact Native.Chart.begins ..
     unfold regal; rw [map_add,map_smul,Pi.add_apply,Pi.smul_apply, hi]; have hp:v=Tilt.wah G A:= (up ..).symm; rw [hp,show t • (tint G _ x i+s • (b.2-b.1)) = A.2+A.1.2-A.1.1 from (by unfold A; rw [smul_add]; dsimp only [Prod.smul_snd,Prod.smul_fst]; rw [smul_smul, mul_comm s t, smul_sub]; abel)]; exact h₁.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hP 2) h.pos)
lemma taper (s:ℝ) (hs:|s| ≤ 1) : postcard G n t (reset z t x s)= gauge (fun y=> G.lieExp ((s*t) • (-z y))) (postcard G n t x):=by
    have hv(i):=firm z x h ht hv hz hc s hs i; funext i; unfold postcard Lattice.gauge; rw [Work.F03.represent_link,Work.F03.represent_link,map_smul,map_smul,Pi.smul_apply,Pi.smul_apply, ← (hv _).1,(hv _).2.1]; unfold ran Native.Chart.hit; rw [show axisEquiv.symm (Exterior.coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; dsimp only; rw [smul_neg _ (z (i.1 + step _)),Work.F03.exp_neg_color,inv_inv]
lemma pinch(s:ℝ)(hs:|s| ≤ 1): ‖tint G _ (reset z t x s-regal z x s)‖ ≤ D*t*R^2:=by
    have hp := fun i=> (firm z x h ht hv hz hc s hs i)
    refine pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg h.pos ht.le) (sq_nonneg _))|>.mpr fun i=>?_; apply le_of_mul_le_mul_left _ ht
    have hx:=hp i|>.2.2; change ‖Native.Chart.head G (ran z i) _-t • _‖ ≤ _ at hx; nth_rw 1 [← Real.norm_of_nonneg ht.le]; rw [←norm_smul, map_sub, Pi.sub_apply,smul_sub, ← (hp i).1]; refine le_trans hx ?_; exact le_of_eq (by ring)
variable (hb:Beam G E)(hk:t*R<E)
include hb hk
lemma wake :reset z t x 0=x :=by
     unfold reset; rw [zero_mul]; have hx(i:Body 1 n): ‖(tint G _) (t • x) i‖<E:=by rw [map_smul,Pi.smul_apply,norm_smul,Real.norm_of_nonneg ht.le]; exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans hv) ht.le) hk
     rw [(Aqua.year z _ hb hx).1, inv_smul_smul₀ ht.ne']
lemma vital (s:ℝ)(hs:|s| ≤ 1)(hy:∀ i:Body 1 n, ‖tint G _ (t • reset z t x s) i‖<E) :HasDerivAt (reset z t x) (speedsK z (t • reset z t x s)) s:=by
    let g:=reset z t x s; have hv': t • reset z t x s=cones z (s*t,t • x):= smul_inv_smul₀ ht.ne' _
    let P(v:ℝ):= coneT z (v,(m) (t • x)); let Z:= t•reset z t x s; have he(i:Body 1 n):=firm z x h ht hv hz hc s hs i; have hp : HasDerivAt P (fun i=>Native.Chart.speed G (ran z i) (tint G _ Z i)) (s*t):=by
         apply hasDerivAt_pi.mpr; intro i; have he : tint G _ Z i= Native.Chart.head G (ran z i) (s*t,t • (m x i)):=by unfold Z; rw [map_smul,Pi.smul_apply,←(he i).1]
         rw [he]; change HasDerivAt (fun s:ℝ=> Native.Chart.head G (ran z i) (s,(tint G _) (t • x) i)) _ _; rw [map_smul,Pi.smul_apply]; apply speedK G _ _ hb (he ▸ hy i); exact ((firm z x h ht hv hz hc s hs i).2.1) -- explicit
    have ht':HasDerivAt (fun s:ℝ=> s*t) t s:=by simpa using (hasDerivAt_id' s).mul_const t
    have hh:= ((m).symm.hasFDerivAt.comp_hasDerivAt s (hp.scomp s ht')).const_smul (t⁻¹); rw [map_smul,inv_smul_smul₀ ht.ne'] at hh; exact hh
end YM.MSbar.Tilt
