import YM.QuadraticLocal.Sunrise.Hat
import YM.QuadraticLocal.Sunrise.Launch
-- Census pure symbol-mode. For true report general weight combine disjoint product from lens_book.
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise.Focus
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module Push AllOrder.Ink.Money
open Marker Multi Comparison.RG02 Comparison.RG02.Cumulants
open scoped BigOperators Topology Classical ContDiff
variable {n:Side} {V ι α: Type}[Fintype α][Fintype ι][DecidableEq ι] [Fintype V][DecidableEq V] (T:Finset ι) (J:Census V) (p:ι→ Poly J)
local notation "I"=> (α⊕ι)
local notation "U"=>rule (α⊕ι) n
local notation "K"=> Leaf n (α⊕ι)
variable {a C D:ℝ}{k:ℕ}
local notation "ϑ"=> ι → ℝ
local notation "σ"=> sustain (α:=α) (n:=n)
local notation "Ξ"=> Scatter.transmit J p
variable (v:rule (α⊕ι) n)
def census (ι:Type)[Fintype ι][DecidableEq ι]: Census ι:= ⟨univ,mem_univ _,fun _=>mem_univ _,fun _ _ _=>mem_univ _⟩
local notation "F₀"=> census ι
abbrev onto (T:Finset ι): (census ι).Mode:= ⟨T,mem_univ _⟩
lemma mergedR (i j q:J.Mode)(h:Poly.merges i j q)(z z':ℂ): Poly.send i z * Poly.send j z'=Poly.send q (z*z'):=by
 ext1 p; rw [Poly.part_send]; change (Poly.prod _ _).part p=_; rw [Poly.cart]; split; next ht=> exact (if_pos (Subtype.ext (ht.2.symm.trans h.2))).symm
 next he=> exact (if_neg (fun ht : p=q =>he (ht.symm ▸ h))).symm
lemma no_merge (x:Hot J)(z:ℂ): (Poly.send x.val z)^2=0:=by
 ext1 i; rw [pow_two]; change (Poly.prod _ _).part _=0; rw [Poly.cart]; refine if_neg (fun h=>?_); obtain ⟨i',hi⟩:= x.property; exact Finset.disjoint_left.mp h.1 hi hi
abbrev detailI (i:ι): Hot (census ι):= ⟨onto {i},Finset.singleton_nonempty _⟩
local notation "v'"=> detailI (ι:=ι)
abbrev pose (i:ι): Poly (census ι):= Poly.send (detailI i).val 1
lemma collects : ∏ i∈T,pose i=Poly.send (onto T) 1:= by
 induction T using Finset.induction_on with
 | empty=> rw [prod_empty]; rfl
 | insert i j hi ih=>
    have he: Poly.merges (onto {i}) (onto j) (onto (insert i j)):= by unfold Poly.merges; simp [onto,hi];
    rw [Finset.prod_insert hi, ih, show pose i= _ from (show pose i=Poly.send (onto {i}) 1 from rfl), mergedR (census ι) _ _ _ he,one_mul]
lemma picks {f:U→ℝ}(h:Rank (rule (α⊕ι) n) k f) : (Scatter.transmit (census ι) pose (fun z:ι→ℝ=> f ((σ z) v))).part (onto T)=(Complex.ofReal (lens T k f v)):= by
 rw [(lens_book F₀ pose v (fun i:ι=> no_merge F₀ (detailI i) 1) h).2, Poly.part_sum]; simp_rw [collects,Poly.part_smul,Poly.part_send]; simp [onto,mul_ite]
lemma weight (w:ι→ℕ)(x:ι): Launch.index F₀ w (detailI x).val=w x:= by unfold Launch.index;simp [detailI,onto]
end YM.QuadraticLocal.Sunrise.Focus
