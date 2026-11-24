import YM.MSbar.Loop.Reaches
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Group.Basic

/-! Markov-free Fourier incidence identity approximation. On compact bands one can use
analytic extension in dimension, but only if the tree joining relations use *common routing*.
Use approximant on a subgroup with growing finite portion meeting every compact support. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Finsupp Super Finset Filter Set MeasureTheory
open scoped BigOperators Classical Topology ENNReal
variable {M:Type*} [AddCommGroup M] [MeasurableSpace M] [TopologicalSpace M] {μ:Measure M}
structure Snap (M:Type*) [AddCommGroup M] [MeasurableSpace M] [TopologicalSpace M] (μ : Measure M) where
   clan : ℕ→AddSubgroup M
   layer : ℕ→Finset M
   δ : ℕ→ℝ
   nonneg : ∀ n,0≤δ n
   snap : ℕ→ M→ M
   mem (n) (v : M) : snap n v ∈ clan n
   sub (n) (v : M) : v∈ layer n → v∈ clan n
   eventually (K:Set M) : IsCompact K → ∀ᶠ n in atTop,K ∩ clan n ⊆ layer n
   cover (K:Set M) : IsCompact K → ∃ H:Set M, IsCompact H ∧ ∀ᶠ n in atTop,snap n ⁻¹' K ⊆ H
   knows (n : ℕ)(x : M) : x∈layer n→MeasurableSet (snap n ⁻¹' {x})
   plays (n : ℕ)(x : M) : x∈layer n→ μ (snap n ⁻¹' {x})= ENNReal.ofReal (δ n)
   seq (x:M): Tendsto (fun n=>snap n x) atTop (𝓝 x)
namespace Snap
variable (B : Snap M μ) {K:Set M}

def charge (n : ℕ)(f:M→ℂ) := (↑(B.δ n):ℂ)*∑ v∈B.layer n,f v
-- no continuity of f in reading at compact snap grid
lemma book (hK:IsCompact K) : ∀ᶠ n in atTop,∀ f : M→ℂ, Function.support f ⊆ K → Integrable (f ∘ B.snap n) μ ∧ B.charge n f=∫ x,f (B.snap n x) ∂μ:=by
   filter_upwards [B.eventually K hK] with n hn f hf
   let R := B.snap n; let P(v:M) := R ⁻¹' {v}; let C (v:M):= (P v).indicator (fun _=> f v)
   have he:f ∘ R=∑ v∈ B.layer n,C v:=by
       ext1 x; rw [Finset.sum_apply]; by_cases h:R x∈B.layer n; swap
       · change f (R x)=_; have ht:f (R x)=0:= by_contra fun hx=> h (hn (show R x∈K∩ B.clan n from ⟨hf hx,B.mem n x⟩)); rw [ht]; symm
         exact Finset.sum_eq_zero fun i hi=> Set.indicator_of_notMem (show x∉ P i from fun hz=> h ((show R x=i from hz) ▸ hi)) _
       rw [Finset.sum_eq_single_of_mem (R x) h (fun i hi hv=> Set.indicator_of_notMem (show x∉ P i from fun hz=> hv (Eq.symm (show R x=i from hz))) _)]; exact Eq.symm (Set.indicator_of_mem (mem_preimage.mpr (mem_singleton (R x))) (fun _=>f (R x)))
   have hp(v:M)(h:v∈B.layer n): Integrable (C v) μ:= (integrable_indicator_iff (B.knows n v h)).mpr (integrableOn_const ((B.plays n v h).trans_ne ENNReal.ofReal_ne_top))
   change Integrable (f ∘ R) μ ∧ B.charge n f=∫ x,(f ∘ R) x ∂μ; rw [he]; simp_rw [Finset.sum_apply]
   refine ⟨by simpa only [← Finset.sum_apply] using integrable_finsetSum _ hp,?_⟩; unfold charge; rw [integral_finsetSum _ hp, Finset.mul_sum]; apply Finset.sum_congr rfl
   intro x hx; unfold C; rw [integral_indicator (B.knows n x hx),setIntegral_const,Measure.real,(B.plays n x hx),ENNReal.toReal_ofReal (B.nonneg _)]; rfl

-- helper boundedness of sampled kernels. Ask convergence to same along EVERY subsequence.
variable [T2Space M] [FirstCountableTopology M] [BorelSpace M] [IsLocallyFiniteMeasure μ]
variable {b : ℕ→ℕ} (ht:Tendsto b atTop atTop) {f : ℕ→M→ℂ} {g:M→ℂ}
    (hd:∀ x:M, ∀ (k:ℕ→ℕ)(v:ℕ→ M), Tendsto k atTop atTop→ Tendsto v atTop (𝓝 x)→ (∀ i,v i∈B.clan (b (k i))) → Tendsto (fun i=> f (k i) (v i)) atTop (𝓝 (g x)))
    (h :∀ i, Function.support (f i)⊆ K) (hk:IsCompact K)
include hd hk
omit [T2Space M] [BorelSpace M] [IsLocallyFiniteMeasure μ] in
lemma affordable : ∃ C:ℝ,0≤C ∧ ∀ᶠ n in atTop,∀ v:M,v∈K→v∈B.clan (b n)→ ‖f n v‖ ≤ C:= by
   by_contra H; push Not at H
   have he(i:ℕ): ∃ k≥i, ∃ v∈K,v∈B.clan (b k) ∧ i< (‖f k v‖:ℝ):= frequently_atTop.mp (H i (Nat.cast_nonneg _)) i
   choose w hw v hV hv hN using he
   obtain ⟨x,hx,a,ha,hA⟩:= hk.tendsto_subseq hV
   have hW : Tendsto w atTop atTop := tendsto_atTop_mono hw tendsto_id
   let u(i):= ‖f (w (a i)) (v (a i))‖
   have hm:=hd x (w∘a) (v∘a) (hW.comp ha.tendsto_atTop) hA (fun i=> hv _); have hT:Tendsto u atTop atTop:= tendsto_atTop_mono (fun i=> (hN (a i)).le) (tendsto_natCast_atTop_atTop.comp ha.tendsto_atTop)
   exact not_tendsto_atTop_of_tendsto_nhds (hm.norm) hT
include ht h hk
lemma goes : Tendsto (fun n=>B.charge (b n) (f n)) atTop (𝓝 (∫ x,g x ∂μ)):=by
   let A n:= f n ∘ B.snap (b n); obtain ⟨C,hC,H⟩:= B.affordable (K:=K) hd hk; have he: ∀ᶠ n in atTop,Integrable (A n) μ ∧ B.charge (b n) (f n)=∫ x,A n x ∂μ:= (ht.eventually (B.book hk)).mono fun n ht=> ht _ (h n)
   refine Tendsto.congr' (he.mono fun n hn=> hn.2.symm) ?_; obtain ⟨P,hP,hJ⟩:= B.cover K hk
   refine tendsto_integral_filter_of_dominated_convergence (P.indicator (fun _=>C)) (he.mono fun n hn=> hn.1.aestronglyMeasurable) ?_ ((integrable_indicator_iff hP.measurableSet).mpr (integrableOn_const hP.measure_lt_top.ne)) (Eventually.of_forall fun a=> ?_)
   · filter_upwards [H,ht.eventually hJ] with n hn ht
     refine Eventually.of_forall (fun x=>?_); let r:=B.snap (b n) x; by_cases hu : A n x=0
     · rw [hu,norm_zero]; exact indicator_nonneg (fun _ _=> hC) x
     have hv:r∈K:= h n hu; rw [Set.indicator_of_mem (show x∈P from ht (mem_preimage.mpr hv))]; exact hn r hv (B.mem _ _)
   exact hd _ id (fun n=>B.snap (b n) a) tendsto_id ((B.seq _).comp ht) (fun _=>B.mem ..)
end Snap
end YM.MSbar.Loops
