import YM.RegulatorIR.Skein.Land

/-!
# Interchanging sums with Γ through finite screens
Column and limits on coefficient. No screen budget beyond finiteness.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Skein
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Train Pupil Cluster Cluster.Brief
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {G:Gauge}{X Y Z:Type}{p r e i k:ℕ}

def Acres (Γ: Curve X Y) (p:ℕ):Prop:=∀ i≤p,∀ x, (quota (fun y:X=>Γ y i x) 1) ≠⊤
variable (Γ:Curve X Y)(A:Acres Γ p)
section Limit
variable (T:Orders X)(HP:∀ i≤p,∀ k,Limits (T i k)) (F:Z↪Y)
include A
lemma chimney (g:Fin r→ℕ)(T:Packet X r)(h:Limits T)(he: charge g≤ p)(y): Summable (fun z=>T z*tracked Γ g z y):=by
 let f(i:Fin r)(x:X):= ‖Γ x (g i) (setting g Y y i)‖ₑ
 obtain ⟨c,hc,h'⟩:=h
 have hf : ∀ i,(∑' x, f i x)≠⊤:= fun i=> by
    have hp: g i ≤ charge g:= Finset.single_le_sum (fun j _=> Nat.zero_le (g j)) (Finset.mem_univ i); rw [← show (quota (fun b:X=>Γ b (g i) (setting g Y y i)) 1)=∑' x:X,f i x from quota_base _]
    exact A (g i) (hp.trans he) _
 apply quota_summable (w:=1) (fun _=>le_rfl) (ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (tallS X r f hf)) ?_)
 rw [quota_base,← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro i;rw [enorm_mul,tracked,Train.units];exact mul_le_mul_left (h' i) _
lemma auraD (g:Fin r→ℕ)(T:Packet X r)(h:Limits T)(he:charge g≤p) : Tendsto (fun l=>series (house F Γ l) g (crop (tile l) T)) atTop (𝓝 (crop F (series Γ g T))):=by
 apply tendsto_pi_nhds.mpr;intro x
 let y:= acrossT F x
 have hv(l:Finset X) : series (house F Γ l) g (crop (tile l) T) x=∑ z∈tent r l,T z * tracked Γ g z y:=by
    rw [series,tsum_fintype]; refine sum_bij (fun a _=> acrossT (tile l) a) (fun a _=> Fintype.mem_piFinset.mpr (fun i=> (a i).property)) (fun _ _ _ _ h=>injectT _ h) ?_ (fun _ _=>rfl)
    intro a ha; exact ⟨fun i=>⟨a i,Fintype.mem_piFinset.mp ha i⟩,mem_univ _,rfl⟩
 have hh:= ((chimney Γ A g T h he y).hasSum.comp (tent_wide (X:=X) r)); convert hh using 1;ext1 i; exact hv i
 rfl
lemma ripple (T:Packet X r) (h:Limits T)(hi:i ≤ p) : Tendsto (fun l=> updateQ (house F Γ l) (crop (tile l) T) i) atTop (𝓝 (crop F (updateQ Γ T i))):=by
 unfold updateQ; rw [crop_sum]; apply tendsto_finsetSum; intro g hg; have ht:= (Gradient.turns_iff _ _).mp hg; subst i; simp only [Gradient.cut,↓reduceDIte]; rw [crop_clock];exact draws_sym (auraD Γ A F g T h hi)
include HP
lemma seal_w (h:e+i≤p): Tendsto (fun l=>Gradient.drawn (house F Γ l) (measureT l T) e i k r) atTop (𝓝 (crop F (Gradient.drawn Γ T e i k r))):=by
 by_cases ht:k+i=r
 · subst r; simp only [Gradient.drawn]; exact ripple Γ A F _ (HP _ (by omega) _) (by omega)
 simp_rw [Gradient.drawn,dif_neg ht]; exact tendsto_const_nhds
lemma texture (hi:i≤p): Tendsto (fun l=>shot (house F Γ l) (measureT l T) i r) atTop (𝓝 (crop F (shot Γ T i r))):=by unfold shot; simp_rw [crop_sum]; apply tendsto_finsetSum;intro j hj; apply tendsto_finsetSum;intro _ _; exact seal_w Γ A T HP F ((Finset.mem_antidiagonal.mp hj).le.trans hi)

variable [Fintype Z] (x:Z→ℝ)
omit HP
lemma tickF (k:ℕ)(hi:k≤p) : Tallied (fun _:Side=> circ Γ (dilute F x)) k:=by
 let V(i:X):= circ Γ (dilute F x) i; let f(z:Tuple Z (k+1))(i:X):= ‖Γ i k (acrossT F z)‖ₑ* ‖noodle x z‖ₑ
 have hf(z):(∑' i,f z i)≠⊤:= by unfold f; rw [ENNReal.tsum_mul_right];apply ENNReal.mul_ne_top; exact (by simpa only [quota_base] using A k hi (acrossT F z));exact enorm_ne_top
 let c(i:X):=∑ z: Tuple Z (k+1),f z i
 refine ⟨c,?_,fun _ i=>?_⟩
 · unfold c; rw [Summable.tsum_finsetSum (fun _ _=> ENNReal.summable)]; exact ENNReal.sum_ne_top.mpr (fun _ _=> hf _)
 change ‖coeff k (V i)‖ₑ≤c i; unfold V circ; rw [PowerSeries.coeff_mk, crops x F, strum, tsum_fintype]; apply (enorm_sum_le ..).trans;apply le_of_eq;apply sum_congr rfl;intro z _;exact enorm_mul ..
include HP
lemma cinema (hi:i ≤ p)(R:Ranks e T) : MvPolynomial.eval x (packed (fun j=> crop F (shot Γ T i j)) (i+e))= rhymeR (circ Γ (dilute F x)) T e i:=by
 let f(l:Finset X):= shot (house F Γ l) (measureT l T) i
 let P(l:Finset X):= MvPolynomial.eval x (packed (f l) (i+e));let r:= circ Γ (dilute F x)
 let H(j:ℕ):= crop F (shot Γ T i j)
 have hh:Tendsto P atTop (𝓝 (MvPolynomial.eval x (packed H (i+e)))):=by
    unfold P; simp_rw [← speaking]; apply tendsto_finsetSum; intro s hs; have ht:= texture (r:=s) Γ A T HP F hi; unfold strum; simp_rw [tsum_fintype];apply tendsto_finsetSum; intro j _; exact (tendsto_pi_nhds.mp ht j).mul_const _
 apply tendsto_nhds_unique hh; unfold P f; simp_rw [fun l=> finite_path (house F Γ l) (measureT l T) (measure_price l T R) i x, rhymeR]; apply tendsto_finsetSum; intro j hj;apply tendsto_finsetSum;intro s hs
 let V:= T j.1 s
 have hp':j.1+j.2=i:=mem_antidiagonal.mp hj
 obtain ⟨c,hc,hC⟩:= HP j.1 (by omega) s
 let t(z:Tuple X s):= V z * coeff j.2 (pip r z)
 obtain ⟨g,hg,hG⟩:= Tallied.multiply (fun i h=>tickF Γ A F x i h) s j.2 (by omega)
 have hv: Summable t:=by
    apply quota_summable (fun _=>le_rfl) (w:=1); rw [quota_base];apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hc hg); rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro u;unfold t;rw [enorm_mul] -- let
    exact mul_le_mul' (hC u) (hG 1 u)
 let τ(l:Finset X):= measureT l T; have hr(l: Finset X)(p:l): circ (house F Γ l) x p=r p.val:=by ext t;rw [circ,coeff_mk]; unfold r;rw [circ,coeff_mk]; exact (crops ..).symm
 have he(l:Finset X): rhyme (circ (house F Γ l) x) (τ l j.1 s) j.2=∑ z∈tent s l,t z:=by
    rw [rhyme,tsum_fintype];refine sum_bij (fun a _=>acrossT (tile l) a) (fun a _=> Fintype.mem_piFinset.mpr fun i=> (a i).property) (fun _ _ _ _ h=> injectT _ h) ?_ ?_
    intro a h; exact ⟨fun i=>⟨a i,Fintype.mem_piFinset.mp h i⟩,mem_univ _,rfl⟩
    intro z _; unfold pip;simp_rw [hr]; rfl
 change Tendsto (fun l=> rhyme (circ (house F Γ l) x) (τ l j.1 s) j.2) _ _
 simp_rw [he];exact hv.hasSum.comp (tent_wide ..)
end Limit

include A
lemma cloister (T:Orders X)(HP:∀ i≤p,∀ r,Limits (T i r))(R:Ranks k T){V:Curve X Y}(B:Acres V p)(h:Gain.Voice Γ V T k p)(he:i ≤p) : shot Γ T i=shot V T i:=by
 ext1 j; ext1 y; by_cases hp:j≤ i+k
 · let L:= Finset.univ.image y;let F:= tile L; let v(r:ℕ):=crop F (shot Γ T i r); let w(r:ℕ):=crop F (shot V T i r)
   have ht: packed v (i+k)=packed w (i+k):=MvPolynomial.funext (fun z=> (cinema Γ A T HP F z he R).trans ((h L z i he).trans (cinema V B T HP F z he R).symm))
   have hc:j∈Finset.range (i+k+1):= Finset.mem_range.mpr (by omega); have hv:= identified (v j) (w j) (crop_symm _ _ (shiftSym _ _ _ _)) (crop_symm _ _ (shiftSym _ _ _ _)) ((Diagram.isolate _ hc).symm.trans ((congr_arg (MvPolynomial.homogeneousComponent j) ht).trans (Diagram.isolate _ hc)))
   exact congr_fun hv fun i=> ⟨y i,mem_image_of_mem _ (mem_univ _)⟩
 rw [show shot Γ T i j=0 from Classical.not_not.mp fun H=>hp (shot_rank R Γ i j H),show shot V T i j=0 from Classical.not_not.mp fun H=> hp (shot_rank R V i j H)]
end YM.RegulatorIR.Skein
