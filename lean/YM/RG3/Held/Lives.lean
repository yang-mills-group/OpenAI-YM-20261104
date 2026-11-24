import YM.RG3.Held.View
import YM.Marker.Truncated

/-!
# Separate external slots (passive test/function columns)

Prohibition rules in R must already include any physical prohibitions when
selecting different markers for the same semantic slot; not a full contact
prescription. This transports tensor test identities *when supplied for
the corrected Deck just like for each input.* Policies outside the window
where this storage is valid (shrinking radii change, testing simplex, lost
preimages, active sector substitutions on test values, Taylor-jet truncation
in addresses) need further models. Passive norm here can be any ℂ normed
space per key; also provide a version for real-multilinear slots for tilings
with hand/reflection or joint real test protocols.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Held
open Lattice Wilson RG Overlay Marker Function Finset MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable (K : Type*) [RCLike K] {V : Type*} [DecidableEq V] (T : V → Type*) [∀ v, AddCommGroup (T v)] [∀ v, Module K (T v)]
variable {E : Type*} [AddCommGroup E] [Module K E]

/-- Require additivity even at exact zeros. E-valued multilinearity with
actual keys; does not follow just from a statement about throughput. -/
structure Letter (s : Finset V) (f : (Π v,T v) → E) : Prop where
  stay x y : (∀ i∈s,x i=y i) → f x=f y
  join x i (hi : i∈s) a b : f (update x i (a+b))=f (update x i a)+f (update x i b)
  scale x i (hi : i∈s) (r : K) a : f (update x i (r • a))=r • f (update x i a)

namespace Letter
variable {K T} {s : Finset V} {f h : (Π v,T v) → E}

lemma still : Letter K T s (0 : (Π v,T v) → E) where
  stay _ _ _ := rfl
  join := by simp
  scale := by simp
lemma const (q : E) : Letter K T ∅ fun _ => q where
  stay _ _ _ := rfl
  join := by simp
  scale := by simp
lemma add (ht : Letter K T s f) (ha : Letter K T s h) : Letter K T s (f+h) where
  stay x y he := congrArg₂ HAdd.hAdd (ht.stay x y he) (ha.stay x y he)
  join x i he a b := by dsimp only [Pi.add_apply]; rw [ha.join x i he,ht.join x i he]; abel
  scale x i he r a := by dsimp only [Pi.add_apply]; rw [ha.scale x i he,ht.scale x i he,smul_add]
lemma neg (he : Letter K T s f) : Letter K T s (-f) where
  stay x y hq := congrArg Neg.neg (he.stay x y hq)
  join x i hi a b := by simp only [Pi.neg_apply,he.join x i hi]; abel
  scale x i hi r a := by simp only [Pi.neg_apply,he.scale x i hi,smul_neg]
lemma linear {E' : Type*} [AddCommGroup E'] [Module K E'] (H : E →ₗ[K] E') (he : Letter K T s f) : Letter K T s fun x => H (f x) where
  stay x y h := congrArg H (he.stay x y h)
  join x i hi a b := by rw [he.join x i hi,map_add]
  scale x i hi r a := (congrArg H (he.scale x i hi r a)).trans (H.map_smul r _)

lemma outside (hf : Letter K T s f) (x : Π v,T v) {i} (hn : i∉s) (z : T i) : f (update x i z)=f x :=
  hf.stay _ _ (fun v hv => update_of_ne (fun (he : v=i) => hn (by rwa [← he])) ..)

end Letter

section Poly
-- [Algebra K ℂ]: could use (NormedAlgebra ℝ ℂ etc). no PSD assumptions.
variable {K} [Algebra K ℂ]
variable {R : Census V}

def Published (x : (Π v,T v) → Poly R) := ∀ i, Letter K T i.val (fun z => (x z).part i)

namespace Letter
variable {T} {s t : Finset V} {f h : (Π v,T v) → ℂ}

lemma cmul (q : ℂ) (hf : Letter K T s f) : Letter K T s fun x => q * f x := hf.linear (Algebra.lmul K ℂ q)

lemma bind (hf : Letter K T s f) (hh : Letter K T t h) (hp : Disjoint s t) : Letter K T (s∪t) (f*h) where
  stay x y h0 := congrArg₂ HMul.hMul (hf.stay x y (fun i hi => h0 _ (mem_union_left _ hi))) (hh.stay x y (fun i hi => h0 _ (mem_union_right _ hi)))
  join x i hs a b := by
    rcases mem_union.mp hs with hi|hi
    · have hm := fun v => hh.outside x (fun hv => disjoint_left.mp hp hi hv) v
      dsimp only [Pi.mul_apply]; rw [hf.join x i hi,hm (a+b),hm a,hm b,add_mul]
    have hm := fun v => hf.outside x (fun hv => disjoint_left.mp hp hv hi) v
    dsimp only [Pi.mul_apply]; rw [hh.join x i hi,hm (a+b),hm a,hm b,mul_add]
  scale x i hs a b := by
    rcases mem_union.mp hs with hi|hi
    · have hm := fun v => hh.outside x (fun hv => disjoint_left.mp hp hi hv) v
      dsimp only [Pi.mul_apply]; rw [hf.scale x i hi,hm (_ • _),hm b,smul_mul_assoc]
    have hm := fun v => hf.outside x (fun hv => disjoint_left.mp hp hv hi) v
    dsimp only [Pi.mul_apply]; rw [hh.scale x i hi,hm (_ • _),hm b,mul_smul_comm]

lemma total {ι : Type*} (q : Finset ι) (g : ι → (Π v,T v) → ℂ) (hf : ∀ i∈q,Letter K T s (g i)) : Letter K T s fun v => ∑ i∈q,g i v := by
  classical
  induction q using Finset.induction_on with
  | empty => simp only [sum_empty]; exact Letter.still
  | insert j q hj ih => simp only [sum_insert hj]; exact (hf _ (mem_insert_self ..)).add (ih fun i hi => hf _ (mem_insert_of_mem hi))
end Letter

namespace Published
variable {T} {x y : (Π v,T v)→Poly R}

lemma zero : Published (K:=K) T (0 : (Π v,T v)→Poly R) := fun _ => Letter.still
lemma sum (h : Published (K:=K) T x) (he : Published (K:=K) T y) : Published (K:=K) T (x+y) := fun i => (h i).add (he i)
lemma const (p : Poly R) (h : ∀ i,i≠R.quiet → p.part i=0) : Published (K:=K) T fun _ => p := by
  intro i; by_cases he : i=R.quiet
  · subst i; exact Letter.const _
  change Letter _ _ _ (fun _ => _)
  dsimp only; rw [h i he]; exact Letter.still
lemma one : Published (K:=K) T (1 : (Π v,T v)→Poly R) :=
  Published.const 1 (fun _ h => by simp [Poly.one_part,h])

lemma smul (r : ℂ) (hf : Published (K:=K) T x) : Published (K:=K) T (r • x) := fun i => (hf i).cmul r

lemma product (hf : Published (K:=K) T x) (he : Published (K:=K) T y) : Published (K:=K) T (x*y) := by
  intro i
  change Letter _ _ _ (fun v => (x v*y v).part i)
  simp only [Poly.part_mul]
  refine Letter.total _ _ fun j _ => Letter.total _ _ fun k _ => ?_
  by_cases hj : Poly.merges j k i
  · simp only [if_pos hj]
    exact hj.2 ▸ (hf j).bind (he k) hj.1
  simp only [if_neg hj]; exact Letter.still

lemma prod {ι : Type*} (q : Finset ι) (x : ι → (Π v,T v) → Poly R) (h : ∀ i∈q, Published (K:=K) T (x i)) :
    Published (K:=K) T fun z => ∏ i∈q, x i z := by
  classical
  induction q using Finset.induction_on with
  | empty => simp only [prod_empty]; exact one
  | insert i q hm ih=> simp only [prod_insert hm]; exact (h _ (mem_insert_self ..)).product (ih fun _ hi => h _ (mem_insert_of_mem hi))

lemma power (h : Published (K:=K) T x) (i : ℕ) : Published (K:=K) T fun z => x z ^ i := by
  induction i with
  | zero => simp only [pow_zero]; exact one
  | succ i ih => simp only [pow_succ]; exact ih.product h

lemma pass [Fintype V] (h : Published (K:=K) T x) : Published (K:=K) T fun z => Poly.pass (x z) := by
  intro i
  simp_rw [Poly.pass,Poly.part_sum,Poly.part_smul]
  exact Letter.total _ _ (fun j _ => (h.power j i).cmul (j.factorial:ℂ)⁻¹)
end Published

section Sums
-- Need `ContinuousConstSMul K ℂ` (not implied unless NormedAlgebra)
variable [ContinuousConstSMul K ℂ]
namespace Letter
variable {T} {s : Finset V}
lemma assembly {ι : Type*} (x : ι → (Π v,T v) → ℂ) (hv : ∀ i,Letter K T s (x i))
    (hs : ∀ z,Summable (fun i => x i z)) : Letter K T s fun z => ∑' i,x i z where
  stay z y h := tsum_congr fun i => (hv i).stay z y h
  join z i he a b := by
    simp only [(hv _).join z i he,(hs (update z i a)).tsum_add (hs (update z i b))] -- names
  scale z i hi a b := by
    simp only [(hv _).scale z i hi,(hs _).tsum_const_smul]
end Letter
namespace Published
variable {T}
lemma assembly {ι} (x : ι → (Π v,T v) → Poly R) (hv : ∀ i,Published (K:=K) T (x i))
    (hs : ∀ z, Summable (fun i => x i z)) : Published (K:=K) T fun z => ∑' i,x i z := by
  intro i
  simp_rw [Poly.share (hs _)]
  exact Letter.assembly _ (fun j => hv j i) (fun z => ((hs z).hasSum.map ((Poly.get i).toLinearMap.toAddMonoidHom) (Poly.part_cont i)).summable)
end Published
end Sums
end Poly
end YM.RG3.Held
