import YM.OPE.Compatible.Porch.Chest
/-! # Roots of purchase log plane -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
open Page
variable {P:I→ Chant G n}{x:I→ℝ}{v:fieldX (Shade G)}{N:Side}{Y Z: CoverConfig G→ℝ}
abbrev twigK {G:Gauge}(v: fieldX (Shade G))(C s:ℝ):Prop:=0 < C ∧ ∀ i:Edge Cover, ‖indexS i v‖ ≤ C * Real.exp (s * Laurent.size i.1)
def seedD (A:CoverConfig G→ℝ)(s:ℝ)(d:ℕ)(p:ℝ):Prop:=∀ (v:fieldX (Shade G)), Quiet v 0→ ∀ c:ℝ,twigK v c s→ ContDiff ℝ ∞ (fun t:ℝ=> A (lotU (t • v)))∧∀ i:ℕ, i≤ d →∀ t:ℝ,‖iteratedDeriv i (fun t:ℝ=>A (lotU (t • v))) t‖≤ p*c^i
lemma plants (G:Gauge)(k d:ℕ)(D s t:ℝ)(hs:0<s)(hp:0<t)(hy:t*d ≤ s/2)(hD:0≤ D):∃ z:ℝ,0 ≤ z∧ ∀ (P:I→ Chant G k)(A:I→ℝ)(c:ℝ), saturate P A s c→ (∀ i,moderateX (P i) D)→ seedD (rhythm P A) t d (z*c):=by
     choose c hc H using fun i:ℕ=> Scallop G k (s/2) _ (half_pos hs) hD i; let C:= ∑ i∈range (d+1),c i
     have hC:0 ≤ C:= sum_nonneg fun i _=> hc i; refine ⟨C,hC,?_⟩; intro P x A h hz v hv b hB; refine ⟨stamped _ _ v h hv hs hz hD,fun i hi j=>?_⟩
     let V(y:I):ℝ:= lawn (P y); let w(y:I):= ‖x y‖*Real.exp (s*V y); have he : 0 ≤ A:= (tsum_nonneg h.1).trans h.2.2; have hb : 0<b:= hB.1
     let F(y:I):=x y * iteratedDeriv i (fun t:ℝ=>verseX (P y) (lotU (t • v))) j
     have hm(y): ‖F y‖ ≤ (b^i*c i) * w y:=by
          have hf :0 ≤ V y:=by unfold V; positivity
          have hZ:=H i (P y) (b*Real.exp (t*V y)) (by positivity) (hz _) v (fun l hl => (hB.2 l).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cashSize _ _ hl)) hp.le)) hb.le)) j
          have hx:0 ≤ c i:=hc _; unfold F; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left hZ (norm_nonneg _)).trans;
          rw [mul_pow, mul_assoc, mul_left_comm _ (c i) _,← mul_assoc (b^i),← Real.exp_nat_mul, ← Real.exp_add]; unfold w; rw [mul_left_comm (b^i*c i) ‖x y‖]; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)) (norm_nonneg _)
          change i*(t*V y)+s/2*V y≤ s*V y; have hz:(i:ℝ)≤d:=Nat.cast_le.mpr hi; have h': t*i≤s/2:=(mul_le_mul_of_nonneg_left hz hp.le).trans hy; linarith only [mul_le_mul_of_nonneg_right h' hf]
     let M:=b^i*c i; have hM:0 ≤ M:=mul_nonneg (pow_nonneg hb.le _) (hc _); have hh:= lyricQ h hs hz hD i hv j; rw [← hh.tsum_eq]; apply (norm_tsum_le_tsum_norm (hh.summable.norm)).trans ((hh.summable.norm.tsum_le_tsum hm (h.2.1.mul_left M)).trans ?_)
     change (∑' (y:I),M*w y)≤_; rw [tsum_mul_left]; apply (mul_le_mul_of_nonneg_left h.2.2 hM).trans; rw [show M * A=c i*A*b^i by unfold M;ring]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (single_le_sum (fun i _=> hc i) (mem_range.mpr (by omega))) he) (pow_nonneg hb.le _)
lemma seedSum (h:seedD Y s i b)(hg:seedD Z s i U): seedD (Y+Z) s i (b+U):=by
     intro p hp c hc; obtain ⟨hx,H⟩:=h p hp _ hc; obtain ⟨hz,ht⟩:= hg p hp _ hc; refine ⟨hx.add hz,fun j hj t=>?_⟩; change ‖iteratedDeriv j ((fun t:ℝ=>Y (lotU (t • p)))+(fun t:ℝ=> Z (lotU (t • p)))) t‖≤_
     rw [iteratedDeriv_add ((hx.of_le (WithTop.coe_le_coe.mpr (le_top))).contDiffAt) ((hz.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt),add_mul]; exact (norm_add_le ..).trans (add_le_add (H j hj t) (ht j hj t))
lemma seedScale (h:seedD Y s i b)(r:ℝ): seedD (r • Y) s i (‖r‖*b):=by
       intro p hp c hc; obtain ⟨hx,H⟩:=h p hp _ hc; refine ⟨hx.const_smul r,fun j hj t=>?_⟩; rw [show iteratedDeriv j _ t=_ from (show iteratedDeriv j (fun t:ℝ=>(r • Y) (lotU (t • p))) t=r • iteratedDeriv j (fun t:ℝ=> Y (lotU (t • p))) t from iteratedDeriv_const_smul ((hx.of_le (WithTop.coe_le_coe.mpr (le_top))).contDiffAt) r), norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (H _ hj _) (norm_nonneg _)
lemma seedSet (K:Finset I)(X:I→ CoverConfig G→ℝ)(p:I→ℝ)(h:∀ j∈ K,seedD (X j) s i (p j)): seedD (∑ j∈K,X j) s i (∑ j∈K,p j):=by
       induction K using Finset.induction_on with
       | empty=>rw [sum_empty,sum_empty];exact fun _ _ _ _=>⟨contDiff_const,fun j _ t=>by change ‖iteratedDeriv j (0:ℝ→ℝ) t‖≤ 0*_; rw [iteratedDeriv_const_zero,norm_zero,zero_mul]⟩
       | insert j K hj ih=>rw [sum_insert hj,sum_insert hj]; exact seedSum (h _ (mem_insert_self ..)) (ih fun i hi=> h _ (mem_insert_of_mem hi))
end YM.OPE.Flume.Script
