import YM.Next.STATIONARY.Lift.Pathways
import Mathlib.Analysis.Convex.Integral
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Zora
open Function Filter Lattice Laurent RG Wilson Stationary Set MeasureTheory Finset
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {o:Lattice.Order} {c:Cover} {j k n ℓ:ℕ}
local notation "C"=>G.Color
local notation "I"=>G.ColorIndex
local notation "K"=>G.El
local notation "b"=>EuclideanSpace.basisFun G.ColorIndex ℝ
set_option quotPrecheck false
-- real cubature before epoch. cost may be large, but fixed demand.
abbrev aim (G:Gauge)(n :ℕ) := Stationary.Ink G n × Stationary.Ink G n
abbrev agenda (G:Gauge)(ℓ:ℕ) := Σ i:Fin (ℓ+1),aim G i.val
local notation "J"=>agenda G ℓ
variable (u:G.El)
protected theorem continuity (a:G.Color): Continuous fun u:K=> G.adjoint u a := G.projectColor.continuous_of_finiteDimensional.comp ((G.continuous_mat.mul continuous_const).mul (continuous_star.comp G.continuous_mat))
-- beverage rank n channels
abbrev core (u:G.El)(s:Stationary.Ink G n)(X:Fin n→G.Color):= ∏ i:Fin n,G.adjoint u (X i) (s i)
abbrev note (a:agenda G ℓ) (u:G.El):= core u a.2.1 (b ∘ a.2.2)
abbrev notes (G:Gauge)(ℓ:ℕ) (u:G.El)(a:agenda G ℓ):=note a u
local notation "M"=>notes G ℓ
local notation "μ"=>G.probHaar
lemma core_continuous (s:Ink G n)(X:Fin n→G.Color): Continuous fun u=>core u s X:= continuous_finsetProd _ fun i _=> (EuclideanSpace.proj (s i)).continuous.comp (Zora.continuity _)
lemma full_path : Continuous (notes G ℓ):= continuous_pi fun a=> core_continuous ..
lemma pricing (G:Gauge)(ℓ:ℕ): ∃ (w:G.El→₀ℝ), ∑ i∈w.support,w i • notes G ℓ i=∫ i, notes G ℓ i ∂G.probHaar:= by
 let M₀:= Submodule.span ℝ (Set.range (notes G ℓ)); letI:= G.probHaar_isProbability; have h:= M₀.convex.integral_mem M₀.closed_of_finiteDimensional (Eventually.of_forall (fun i=> Submodule.subset_span (Set.mem_range_self i))) (show Integrable (notes G ℓ) G.probHaar from full_path.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)); exact Finsupp.mem_span_range_iff_exists_finsupp.mp h
structure Noon (G:Gauge)(ℓ:ℕ) where
   samples : G.El→₀ℝ
   book : ∑ i∈samples.support,samples i • notes G ℓ i=∫ i,notes G ℓ i ∂G.probHaar
lemma born (G:Gauge)(ℓ:ℕ):Nonempty (Noon G ℓ):= ⟨⟨(pricing G ℓ).choose,(pricing G ℓ).choose_spec⟩⟩
namespace Noon
variable (Y:Noon G ℓ)
local notation "u0"=>Y.samples
variable (s:Stationary.Ink G n) (X:Fin n→G.Color)
lemma commutes (t:agenda G ℓ): ∑ i∈Y.samples.support,Y.samples i * note t i=∫ i,note t i ∂μ:= by
 have hp : Integrable M μ := full_path.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
 have he:= congr_fun Y.book t; rw [Finset.sum_apply] at he; exact he.trans (show _= _ from ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:J=>ℝ) t).integral_comp_comm hp).symm) -- orientation
abbrev bump (s:Ink G n)(t:Fin n→G.Color) := ∏ i:Fin n,(t i) (s i)
lemma beams (u:G.El)(n:ℕ)(s:Ink G n)(X:Fin n→G.Color): core u s X= ∑ j:Ink G n,core u s (b ∘ j)*bump j X:= by
    have hv(x:G.Color) (i:I): G.adjoint u x i = ∑ j:I, G.adjoint u (b j) i * x j := by
       let A:= (EuclideanSpace.proj i:G.Color→L[ℝ]ℝ).toLinearMap.comp (G.adjoint u); let B:= (b).toBasis; change A x=_; nth_rw 1 [← B.sum_repr x]; rw [map_sum]; simp_rw [map_smul]; refine Finset.sum_congr rfl fun j _=> ?_; rw [smul_eq_mul, mul_comm]; rfl -- Basis repr
    unfold core bump; simp_rw [show ∀ i:Fin n, _ from fun i=>hv (X i) (s i), Fintype.prod_sum] -- RHS also rewrites risk X literal
    exact Finset.sum_congr rfl fun i hi=> Finset.prod_mul_distrib
lemma hours (hl:n≤ℓ): ∑ i∈Y.samples.support,Y.samples i * core i s X= ∫ i,core i s X ∂μ:= by
 simp_rw [beams (X:=X),Finset.mul_sum]; rw [integral_finsetSum]; swap
 · exact fun i hi=>(core_continuous _ _|>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const _ -- notation
 rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; let t:J:= ⟨⟨n,Nat.lt_succ_of_le hl⟩,s,j⟩; simp_rw [integral_mul_const,← mul_assoc,← Finset.sum_mul]; exact congr_arg (· * bump j X) (Y.commutes t)
def forecast (s: Ink G n)(j:Ink G n):ℝ:= ∑ i∈Y.samples.support,Y.samples i * core i s (b ∘ j)
lemma focused (s : Ink G n)(u:Fin n→G.Color): ∑ j:Ink G n, forecast Y s j*bump j u= ∑ i∈Y.samples.support,Y.samples i *core i s u:= by unfold forecast; simp_rw [beams (X:=u),Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> mul_assoc ..
lemma funded (hl:n≤ℓ): forecast Y s ∈ paints G n:= by
 intro v c; let Γ:K→ℝ:= fun u=>core u s c; let x:=fun i:Fin n=>G.adjoint v (c i); change (∑ j:Ink G n, forecast Y s j*bump j x)=_; rw [focused Y, show (∑ j:Ink G n,forecast Y s j*_)= _ from focused Y s c,hours Y _ _ hl,hours Y _ _ hl]
 have ht (w:K): core w s x=Γ (w*v):= by unfold Γ x core; simp_rw [←G.adjoint_mul]
 simp_rw [ht]; exact integral_mul_right_eq_self _ _
-- sum samples =1 incl G trivial
lemma value : ∑ i∈Y.samples.support,Y.samples i=1:= by
 let s:Ink G 0:= fun i=>nomatch i; simpa only [core,Fintype.prod_empty,mul_one,integral_const, probReal_univ,one_smul] using (hours Y s (fun _=>0) (Nat.zero_le _))
def bill (G:Gauge)(Y:Noon G ℓ)(n:ℕ):= ∑ i : Ink G n,∑ j:Ink G n,|forecast Y i j|
lemma bill_ge {s:Ink G n}: (∑ j:Ink G n,|forecast Y s j|) ≤ bill G Y n:= Finset.single_le_sum (f:=fun i: Ink G n=>∑ j:Ink G n,|forecast Y i j|) (fun i hi => sum_nonneg fun _ _ => abs_nonneg _) (mem_univ s)
end Noon
end YM.Qlocal.Quipu.Zora
