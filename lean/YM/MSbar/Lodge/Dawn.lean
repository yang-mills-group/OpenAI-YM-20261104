import YM.MSbar.Lodge.Halo
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
variable {σ ι M:Type}[Fintype σ][Fintype ι][MeasurableSpace M]{μ:MeasureTheory.Measure M}[MeasureTheory.IsProbabilityMeasure μ]
open MeasureTheory Set Metric
local notation "Π"=>Positions σ
local notation "Λ"=>Positions ι
variable {k p s:ℕ}{a c C w B V ε:ℝ}{n:Side}{F:Positions σ→ℝ}(P:Positions ι→L[ℝ]Positions σ)
variable {m:ℕ}{D:ℝ}
variable {f:ℝ→ℝ}(h:Hat k w V f)(hs:Vase F k B w)(W: M→ Positions σ) (hW:Measurable W)(x: Positions ι) (hv:0≤ w)(hu:1≤V)
local notation "Z"=> F ∘ Clamp f
local notation "Y"=> (fun v:M=> W v+P x)
-- evaluate at Y=0 with gradient correction Compare. Y expectation unweighted hhat. error weighted via tape. Works at μ(Y), ∆center arbitrary.L.Note probability.Measure lemmas.
noncomputable def summit (l:σ→Site n)(a:ℝ)(p:ℕ)(F:List σ→ℝ)(m:ℕ)(C:ℝ): Prop:= ∀ i:σ,Yarn m (fun L:List σ=> |F (i::L)| *swipe l a p (i::L)) ≤ C
variable (l:σ→ Site n) (L:List σ) (g:List σ→ℝ) (t:Positions σ)
variable {T:Set (Positions σ)}
include h hs hv hW
variable (hw:0<w)(he:m+1≤k)(hx: JetTab l a p w (Metric.closedBall 0 w) F m C)
include hw he hx
local notation "G"=> Clamp f ∘Y
lemma primer : ∃ f':List σ→ℝ, (∀ t:List σ, t.length=m+1 → 0≤ f' t ∧ ∀ (W:M→ Positions σ)(x:Positions ι),Measurable W→ |pearl F (Clamp f ∘ (fun v:M=> W v+P x)) t μ| ≤ f' t)∧ summit l a p f' m (C/w^(m+1)):=by
    obtain ⟨hp,g,hg,ht⟩:=hx; let z:= w^(m+1); have hz:0<z:=pow_pos hw _; refine ⟨fun i=> g i/z,fun L hl=>⟨div_nonneg (hg L hl|>.1) hz.le,fun W x hx=>?_⟩,fun i=>?_⟩
    · have hx' := lake (μ:=μ) P h hs W hx x hv L (hl.trans_le he); unfold pearl; refine le_trans (norm_integral_le_integral_norm (μ:=μ) (fun y:M=>buoy F (Clamp f (W y+P x)) L)) ?_; refine le_trans (integral_mono hx'.norm (integrable_const (μ:=μ) (g L/z)) ?_) (by simp); intro i; exact le_div_iff₀ hz|>.mpr (hg L hl|>.2 _ (peak h hv _))
    refine le_trans (le_of_eq (b:=Yarn m (fun T=> g (i::T)*swipe l a p (i::T))/z) ?_) (div_le_div_of_nonneg_right (ht i) hz.le); rw [div_eq_mul_inv,← poker]; apply stitch; intro j hj; rw [abs_of_nonneg (show 0 ≤ g _/z from div_nonneg (hg _ (by rw [List.length_cons,hj])|>.1) hz.le)]; ring
omit he hx
variable (hp: m+2≤ k)(hh:JetTab l a p w (Metric.closedBall 0 w) F (m+1) C)(hY:∀ i:σ, Integrable (fun y:M=> |W y i+(P x) i|) μ ∧ (∫ y:M,|W y i+(P x) i|∂μ) ≤ D)
include hp hh hY
lemma dawn (hd:0≤D)(ha:0≤ a) : summit l a p (fun L:List σ=> pearl F (Clamp f ∘ (fun i:M=> W i+P x)) L μ- buoy F 0 L) m (D*C/w^(m+2)):=by
    obtain ⟨h₀,g,hg,hE⟩:= hh; let T:=Metric.closedBall (0:Π) w; let z:= w^(m+2); have hz:0 < z:=pow_pos hw _; have h0:0∈T:=mem_closedBall_self hv
    let E(l:List σ):=(∑ i:σ, g (l++[i]))*D/z
    let J(L:List σ):= pearl F (Clamp f ∘Y) L μ; have he(L:List σ)(he:L.length=m+1) : |J L-buoy F 0 L| ≤ E L:=by
       let Z₁(y):=(Clamp f ∘ Y) y; let q(y:Π):= F y; let e:= Bakery.glance F L; let U(z:Π):= buoy F z L; have hC(u:Π)(h:u∈T)(i:List σ)(hp:i.length≤k): Bakery.glance F i u=buoy F u i:=by rw [Bakery.glance_read _ (hs.smooth u h) hp]; exact (fEntry (hs.smooth u h) _ hp).symm
       have hl(i:σ):(L++[i]).length=m+1+1:=by simp [he]
       let I(i y):= |Y y i| *(g (L++[i])/z)
       have hv(i):Integrable (fun y=> I i y) μ:= (hY i|>.1).mul_const _
       have hr(y) : |buoy F (Z₁ y) L-buoy F 0 L| ≤ ∑ i:σ,I i y :=by
           let S(v) := g v/z; obtain ⟨s,hs',hq⟩:= Bakery.cutAt (X:=T) (x:=0) (y:=Z₁ y) (f:=F) L (convex_closedBall ..) h0 (peak h ‹0≤w› (Y y)) (fun x hx=> (hs.smooth x hx).of_le (by exact_mod_cast (by omega : L.length+1≤k))) -- syntax
           have hk': L.length ≤ k := he.le.trans (by omega); rw [← hC _ (show Z₁ y∈T from peak h ‹0≤w› _) _ hk',← hC 0 h0 _ hk',hq]; apply le_trans (Finset.abs_sum_le_sum_abs ..); apply Finset.sum_le_sum; intro i _; simp only [_root_.Pi.zero_apply,sub_zero, abs_mul]; -- edit
           refine mul_le_mul (h.value _|>.1) (le_div_iff₀ hz|>.mpr ?_) (abs_nonneg _) (abs_nonneg _)
           rw [hC _ hs' _ (by rw [hl]; omega)]; exact hg _ (hl i)|>.2 _ hs'
       have hx:=lake (μ:=μ) P h hs W hW x (by linarith only [hw]) L (by omega); unfold J pearl E; rw [show buoy F 0 L= (∫ i:M,buoy F 0 L ∂μ) from by simp]; simp only [Function.comp_apply]; rw [← integral_sub (show Integrable _ _ from hx) (integrable_const _)]; refine (norm_integral_le_integral_norm (μ:=μ) (fun y:M=>buoy F (Clamp f (W y+P x)) L-buoy F 0 L)).trans ?_; apply le_trans (integral_mono (hx.sub (integrable_const _) |>.norm) (integrable_finsetSum _ (fun i _=>hv i)) hr); rw [integral_finsetSum _ (fun i _=> hv i),Finset.sum_mul,sum_div]; refine Finset.sum_le_sum fun i _=>?_ ; unfold I; rw [integral_mul_const]; exact (mul_le_mul_of_nonneg_right (hY i|>.2) (div_nonneg (hg _ (hl i)|>.1) hz.le)).trans_eq (by ring)
    intro i; refine (shiny (ι:=σ) m (g:=fun l'=> E (i::l')*swipe l a p (i::l')) (fun k hx=> mul_le_mul_of_nonneg_right (he _ (by rw [List.length_cons,hx])) (effect ..|>.le))).trans ?_
    refine le_trans ?_ (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hE i) hd) hz.le); let G'(k:List σ):=g (i::k)*swipe l a p (i::k); rw [show D*Yarn _ _/w^(m+2)=∑ j:σ,Yarn m (fun T=>D*G' (T++[j])/z) from ?_]; swap;· simp_rw [div_eq_mul_inv, poker, sheen,← Finset.sum_mul,← Finset.mul_sum]; rw [bothEnds] -- inspect
    rw [←scarves]; apply shiny; intro T h'; unfold E;rw [Finset.sum_mul,sum_div,sum_mul]; refine Finset.sum_le_sum fun j _=>?_ ; unfold G'; simp_rw [List.cons_append]; refine (mul_le_mul_of_nonneg_left (show swipe l a p (i::T)≤ swipe l a p (i::(T++[j])) from ?_) (show 0 ≤ (g (i::(T++[j]))*D)/z from div_nonneg (mul_nonneg (hg _ (by simp [h'])|>.1) hd) hz.le)).trans_eq ?_; swap; · ring -- inspect goal meta
    refine w_more (intr ?_) ha _; unfold Whisk.zone; gcongr; simp [List.map_append]
end YM.MSbar.Lodge
