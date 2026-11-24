import YM.X.Site.Print
/-!
# bird decay & convergence
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Print
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric
open Reed Stems Hinge Braid Fielding
open scoped Topology BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {n:Side} {k m v:ℕ} {G:Gauge}
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "H"=> Hair G
variable (x y z:Cover)(f g:Fan G)(p:Hair G)(A:Brush G)
def scale (n:Side)(x y:Cover):ℝ:= mass (wrap n x) (wrap n y)
lemma scale_pos : scale n x y≥1 := mass_pos ..
lemma scale_le : scale n x y ≤ scale n (x+z) y +street z:= by
   simp only [scale,mass_eq,map_add]; let k:=wrap n z; let u:=wrap n x; let v:=wrap n y; have hz:= wrap_rotate (n:=n) z; have he:= pdist_triangle (u+k-v) (-k); rw [pdist_neg,show u+k-v+-k=u-v by abel] at he
   exact_mod_cast (show 1+pdist (u-v)≤1+pdist (u+k-v)+street z from by unfold k at *; omega)
lemma scale_fee : scale n x y ≤ scale n (x+z) y*day z:= by
   refine (scale_le x y z).trans ?_; nlinarith only [scale_pos (n:=n) (x+z) y, Nat.cast_nonneg (α:=ℝ) (street z), show day z=1+(street z:ℝ) from rfl]
variable {B:GridF}
include hq
lemma cost (h:B ∈ bird k): ∃ c:ℝ,0 ≤ c∧ ∀ᶠ i:ℕ in Fℕ,∀ x y:Cover, ‖B (side q i) x y‖* scale (side q i) x y ^(2+k) ≤ c:= by
    induction h using Submodule.span_induction with
    | mem P hp=>
       obtain ⟨D,hD,z,rfl⟩:=hp; rw [← hD]; obtain ⟨c,hc,HX⟩:= torus_rate (paths hq) D; let b:=D.length; refine ⟨c*day z^(2+b),by have hh:=day_pos z; positivity,?_⟩; filter_upwards [HX] with i hi x y; let n:=side q i; let p:= wrap n (x+z)-wrap n y; let s:=scale n (x+z) y; have hs:s>0:= zero_lt_one.trans_le (scale_pos (n:=n) (x+z) y)
       have he : 1+pdist p=s:= (mass_eq ..).symm; have hf: graphK D z n x y= Interval.grads D green p:= by unfold graphK; rw [show x-y+z=x+z-y by abel,map_sub]
       specialize hi p; change |Interval.grads D green p| ≤ c / (1+pdist p:ℝ)^(2+b) at hi; rw [he, le_div_iff₀ (pow_pos hs _), ← hf] at hi
       calc _ ≤ ‖graphK D z n x y‖ * (s*day z)^(2+b):= by have hz: scale n x y≥0:= zero_le_one.trans (scale_pos (n:=n) x y); change ‖graphK D z n x y‖*scale n x y^(2+b)≤ _; gcongr; exact scale_fee ..
            _ ≤ _ := by rw [mul_pow,← mul_assoc,Real.norm_eq_abs]; gcongr
    | zero=> exact ⟨0,le_rfl,by simp⟩
    | add a d ha hb t u=> obtain ⟨c,hc,t⟩:=t; obtain ⟨r,hr,u⟩:=u; refine ⟨c+r,add_nonneg hc hr,?_⟩; filter_upwards [t,u] with i hi hp x y; let b:= side q i; let k':=2+k; let w:= scale b x y^k'; change ‖a b x y + d b x y‖*w≤c+r; apply (mul_le_mul_of_nonneg_right (norm_add_le ..) (pow_nonneg (zero_le_one.trans (scale_pos (n:=b) x y)) _)).trans; rw [add_mul]; exact add_le_add (hi ..) (hp ..)
    | smul a p h t=> obtain ⟨c,hc,t⟩:=t; refine ⟨‖a‖ * c,by positivity,?_⟩; filter_upwards [t] with i hi x y; simp only [Pi.smul_apply,norm_smul, mul_assoc]; gcongr; apply hi
lemma glides {x y:E4}{f g:Fielding.Walk}(h:B∈bird k)(ht:x≠y)(hf:plot q f x)(hg:plot q g y): Released (fun i=> B (side q i) (f i) (g i) / epsilon q i^(2+k)):= by
    induction h using Submodule.span_induction with
    | mem P h=>
       obtain ⟨D,h,z,rfl⟩:=h; rw [← h]; let l:= f-g+(fun _:ℕ=>z); have hp : plot q l (x-y):= by rw [← add_zero (x-y)]; exact (plot.sub hf hg).add (plot.constant hq z)
       refine ⟨_,rpath_casual (paths hq) D (x-y) (sub_ne_zero.mpr ht) (fun i=> wrap (side q i) (l i)) ?_⟩; apply hp.congr'; exact (plot_lift hq hp).mono (fun i he=> by exact congr_arg (spot (epsilon q i)) he.symm)
    | zero=> simp only [Pi.zero_apply,zero_div]; exact Released.zero
    | add a d ha hb t u=> simp_rw [Pi.add_apply,add_div]; exact t.add u
    | smul a p h t=>simp only [Pi.smul_apply, smul_div_assoc]; exact t.smul ⟨a,tendsto_const_nhds⟩
end YM.PositionX.Print
