import YM.Work.F03.Transport
import YM.QuadraticLocal.Poetry.Vernal
/-!
# Color orientation economic.Project real packets
 Average simple R.A.Atoms, same stencil, B.Regular reuse. Implement integration provenance
 plus exact sampling rule shared by ALL atoms (r≤d). This avoids imposing measurable structure
 on owners before final presentation.Re use.W.Norm.Non-model remains unprojected.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Texture
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Push Stationary MeasureTheory Gauge
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{k N : ℕ} {n:Side}
local notation "μ"=> G.probHaar
variable (q:Atom G k) (u:G.El)
local notation "I"=> G.ColorIndex
abbrev Tooth (G:Gauge)(k:ℕ):= Fin k → G.ColorIndex
local notation "J"=> Tooth G k
-- recipe basis
local notation "B"=> EuclideanSpace.basisFun (I) ℝ
lemma baseC (v:G.Color) : ∑ i:I, v i • B i=v:= by
  refine Eq.trans ?_ ((B).sum_repr v); apply Finset.sum_congr rfl; intro i _; rw [EuclideanSpace.basisFun_repr]
def clip (k:ℕ)(t s:Tooth G k):ℝ:= ∏ i:Fin k, G.adjoint u (B (s i)) (t i)
local notation "ψ" u:max i:max=> Texture.clip (G:=G) u i
-- monomial evaluation from BICY. Thermal budget power.Vertex.S.Boom.
lemma sees (q:Tooth G k) (v:Fin k→G.Color) : (∏ i:Fin k, G.adjoint u (v i) (q i))= ∑ t:J, clip u k q t *∏ i:Fin k, v i (t i):= by
 have hx(i j) : G.adjoint u (v i) j=∑ t:I, (G.adjoint u ((B) t) j)*v i t:=by
     let P:= EuclideanSpace.proj (𝕜:=ℝ) (q i); let X:= ContinuousLinearMap.toLinearMap (EuclideanSpace.proj (𝕜:=ℝ) (ι:=I) j) ∘ₗ G.adjoint u; have h:X (v i)=∑ t:I, v i t * X (B t):=by rw (occs:=.pos [1]) [← baseC (G:=G) (v i)]; rw [map_sum]; simp_rw [map_smul,smul_eq_mul]
     refine Eq.trans h ?_; exact Finset.sum_congr rfl (fun t _=> mul_comm _ _)
 simp_rw [hx]; rw [Fintype.prod_sum]; refine Finset.sum_congr rfl (fun i _=>?_); simp_rw [Finset.prod_mul_distrib]; rfl
lemma phone (k:ℕ)(v w:Tooth G k) : Continuous (fun u:G.El=> Texture.clip u k v w):= by
    unfold Texture.clip; apply continuous_finsetProd; intro i _; let f:=EuclideanSpace.proj (𝕜:=ℝ) (v i); have hi(i':I): Continuous (fun u:G.El=>G.adjoint u (B i')):= G.projectColor.continuous_of_finiteDimensional.comp ((G.continuous_mat.mul continuous_const).mul G.continuous_mat.star); exact f.continuous.comp (hi _)
lemma bill (k:ℕ)(v w:Tooth G k) (u:G.El): ‖Texture.clip u k v w‖ ≤ 1:= by
   rw [Texture.clip, Real.norm_eq_abs, Finset.abs_prod]; refine Finset.prod_le_one (fun i _=> abs_nonneg _) (fun i hi=>?_); exact (PiLp.norm_apply_le ..).trans_eq ((G.norm_adjoint u ((B) (w i))).trans ((B).norm_eq_one _)) -- infer
section sample
variable (G N)
abbrev Locale (G:Gauge)(N:ℕ):= (i:Fin (N+1)) × (Tooth G i.val) × (Tooth G i.val)
local notation "ϕ"=> Locale G N
private def moments (u:G.El) (i:ϕ):ℝ:= clip u i.1.val i.2.1 i.2.2
variable {G N}
lemma hymn (k : ℕ)(v w:Tooth G k): Integrable (fun u:G.El=>clip u _ v w) G.probHaar:= (phone _ v w).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
variable (G N)
def Spray (P : G.El →₀ ℝ)(N:ℕ) := ∀ k≤N,∀ i j: Tooth G k,(∫ u:G.El, Texture.clip u k i j ∂G.probHaar)=∑ i'∈ P.support,(P i') * Texture.clip i' k i j
lemma samples :∃ P:G.El →₀ ℝ, Spray G P N:= by
 let z:=moments G N; let X:= Submodule.span ℝ (Set.range z); let v:=∫ u:G.El,z u ∂G.probHaar; let f(u:G.El): X:= ⟨z u,Submodule.subset_span ⟨u,rfl⟩⟩; haveI : CompleteSpace X:= FiniteDimensional.complete ℝ _; have hp:Continuous z:= continuous_pi fun i:ϕ=>phone ..; have hz:= hp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)|> (fun h : Integrable z μ=>h);
 have he: v∈X := by
    let u:= ∫ x:G.El,f x ∂μ; have hu:v=X.subtypeL u:= X.subtypeL.integral_comp_comm ((show Continuous f from hp.subtype_mk _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)); rw [hu]; exact u.property
 obtain ⟨L,hL⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp he; refine ⟨L,fun k hk i j=>?_⟩; let q:ϕ:=⟨⟨k,by omega⟩,i,j⟩; have hh:v q=∫ u:G.El,z u q ∂μ:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) q).integral_comp_comm hz|>.symm; rw [show (∫ u:G.El,Texture.clip u k i j ∂G.probHaar)=_ from hh.symm,← hL]; change (∑ i∈L.support,L i • z i) q=_; rw [Finset.sum_apply]; rfl
end sample
end YM.QuadraticLocal.Poetry.Texture
