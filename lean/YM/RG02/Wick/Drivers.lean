import YM.RG02.Wick.Connectivity
import YM.RG02.Marker.Linear
import YM.Next.RANK.Common

/-!
Cumulants of any polynomial drivers. `stellar_atoms` to specify leg/vertex
sums including rooted data, `spelling` gives existence of decompositions for
finite indexing and arity without quantitative estimates. To carry those sums
through LOG use multilinearity at the indicated mode. Then CONNECTED termwise
in a precise sense (cuts) by `only_jointly`. This includes using Jacobian
vertices, deterministic background, and the same field/physical predictor
tag in multiple terms of the calculation. Supply *actual* disjoint test
for tag dependencies. No implicit estimates.
-/
set_option autoImplicit false
open YM.Primitives.GCC.Anchor
noncomputable section
namespace YM.RG02.Wick
open Marker Multi Finset Marks Actor Function Extra.Trajectories Next.Rank Next.Rank.Normal
open scoped Classical BigOperators
variable {A T W V : Type}[DecidableEq V]{R : Census V}

def jointly (μ : (T → ℂ)→ₗ[ℂ]ℂ)(q : T → Symmetric W) : (T→poly W) →ₗ[ℂ] ℂ where
  toFun a := μ fun i => blend (q i) 0 (a i)
  map_add' x y := by simp_rw [Pi.add_apply,map_add]; apply μ.map_add
  map_smul' c x := by simp_rw [Pi.smul_apply,map_smul]; apply μ.map_smul

theorem jointly_of_unit {μ : (T → ℂ)→ₗ[ℂ]ℂ}(h : μ 1=1)(q : T → Symmetric W) : jointly μ q 1=1 := by
  change μ (fun i => blend (q i) 0 1)=1; simpa using! h

def stellar (μ : (T → ℂ)→ₗ[ℂ]ℂ)(q : T → Symmetric W)(f : V → T → poly W) : Poly R :=
   Poly.inject fun x => jointly μ q (∏ i∈x.val,f i)

lemma stellar_quiet {μ : (T → ℂ)→ₗ[ℂ]ℂ}(h : μ 1=1)(q : T → Symmetric W) (f : V → T → poly W) :
    (stellar μ q f).part R.quiet=1 := by
   change jointly μ q (∏ i∈∅,f i) = _
   rw [prod_empty,jointly_of_unit h]

section
variable [Fintype V]

/-- Multilinearity through the monomial presentations. Apply also
with a different presentation at each root but all powers at the same mark. -/
lemma stellar_sum {μ : (T → ℂ)→ₗ[ℂ]ℂ}(h : μ 1=1)(q : T → Symmetric W) {D : V → Type}[∀ i,Fintype (D i)]
    (F : ∀ i,D i→T → poly W)(f : V → T → poly W)(s : R.Mode)(hc : ∀ i∈s.val,f i=∑ j:D i,F i j):
    (connected (stellar μ q f)).part s = ∑ z : (i : (↑s.val)) → D (i:V),
      (connected (stellar μ q (fun i => if H : i∈s.val then F i (z ⟨i,H⟩) else f i))).part s := by
   let U := fun x : V → T → poly W => (connected (stellar μ q x)).part s
   apply picked s.val f F U
   intro i hi y
   apply Marks.piece (stellar_quiet h q _) univ (fun j => stellar μ q (update y i (F i j))) (fun _ _ => stellar_quiet h q _) i s hi
   · intro t _ hv
     change jointly μ q (∏ j∈t.val, Function.update y i (f i) j) = ∑ u:D i, (stellar _ _ _).part t
     have HE : ∏ j∈t.val, Function.update y i (f i) j =∑ u:D i, ∏ j∈t.val, Function.update y i (F i u) j := by
        have hy p : ∏ j∈t.val, Function.update y i p j=p*∏ j∈t.val.erase i,y j := by
          rw [← Finset.mul_prod_erase _ _ hv,Function.update_self]; congr 1
          exact prod_congr rfl fun j hj => update_of_ne (mem_erase.mp hj).1 ..
        simp_rw [hy,hc i hi,sum_mul]
     rw [HE,map_sum]
     rfl
   intro t _ hn u _; change jointly μ q _=jointly μ q _
   congr 1; exact prod_congr rfl fun j hj => by simp [update_of_ne (ne_of_mem_of_not_mem hj hn)]
end

section atoms
variable [DecidableEq A] [Fintype A]

/-- Use this with D a finite-product enumeration or canonical supported
sums. `i` still carries ALL its own legs. -/
lemma stellar_atoms (μ : (T → ℂ)→ₗ[ℂ]ℂ)(q : T → Symmetric W) (o : A→V)(c : V → T → ℂ)(ℓ : T → A → W)
    (f : V → T → poly W)(x : Finset V)
    (h : ∀ i∈x,∀ t, f i t=c i t • glyphs (ℓ t) (arms o {i})) : UpTo x (stellar (R:=R) μ q f) (monomials o c q ℓ μ) := by
   intro s hs
   change μ (fun t => blend _ _ ((∏ j∈s.val,f j) t)) = μ _
   congr 1; funext t; rw [Finset.prod_apply]
   have ht (u : Finset V)(he : u⊆x) : ∏ i∈u,f i t=(∏ i∈u,c i t) • glyphs (ℓ t) (arms o u) := by
      induction u using Finset.induction with
      | empty => rw [prod_empty,prod_empty]; simp only [arms,notMem_empty,one_smul,glyphs]; simp
      | insert i v hi ih =>
          have hu : arms o (insert i v)= arms o {i} ∪ arms o v := by ext; simp
          have hd : Disjoint (arms o {i}) (arms o v) := Finset.disjoint_left.mpr fun j hj hh => hi ((mem_singleton.mp (arm_of.mp hj)) ▸ arm_of.mp hh)
          rw [prod_insert hi, prod_insert hi,h i (he (mem_insert_self ..)), ih (Subset.trans (subset_insert ..) he),hu]
          simp only [glyphs,prod_union hd,smul_mul_smul_comm]
   rw [ht s.val hs,map_smul]; rfl
end atoms

-- For a finite tag law, don't need assuming monomial decomposability.
theorem spelling [Fintype T] (f : T → poly W) :
    ∃ (s : Finset (W →₀ ℕ))(n : (W →₀ ℕ)→ℕ)(v : ∀ i:W→₀ℕ,Fin (n i)→W)(a : (W →₀ ℕ) → T → ℂ),
       f = ∑ i∈s,fun x => a i x • glyphs (v i) univ := by
   classical
   let s:= univ.biUnion fun t:T => (f t).support
   let n := fun i:W→₀ℕ => i.sum (fun _ k=>k)
   choose v hv using fun i:W→₀ℕ => Common.letter i
   refine ⟨s,n,v,(fun i t => MvPolynomial.coeff i (f t)),?_⟩
   funext t
   have hh (i) : MvPolynomial.monomial i (MvPolynomial.coeff i (f t)) = MvPolynomial.coeff i (f t) • glyphs (v i) univ := by rw [← hv i, ← map_smul,smul_eq_mul,mul_one]
   rw [Finset.sum_apply]
   change f t=∑ i∈s, MvPolynomial.coeff i (f t) • glyphs (v i) univ
   simp_rw [← hh]
   nth_rw 1 [(f t).as_sum]; apply sum_subset (subset_biUnion_of_mem (fun t:T => (f t).support) (mem_univ t)); intro i _ hi; rw [MvPolynomial.notMem_support_iff.mp hi,map_zero]

/-- In turn both the vertex and the *line* supports may be telescope sums,
using the same underlying tags. Use values on `L`,V inl, pair inr. -/
def rises [DecidableEq A][Fintype A](o : A→V)(g : V⊕Multi.Hot (full A)→ T → ℂ)
    (μ : (T→ℂ)→ₗ[ℂ]ℂ) : Poly (together R (Lines A)) := terms o (fun i => g (.inl i)) (fun i => g (.inr i)) μ

lemma rises_part [DecidableEq A][Fintype A] (o : A→V)(g : V⊕Multi.Hot (full A)→ T → ℂ)
    (μ : (T→ℂ)→ₗ[ℂ]ℂ)(s : (together R (Lines A)).Mode) :
    (rises o g μ).part s = if Paired o s then μ (∏ i∈s.val,g i) else 0 := by
   change (if Paired o s then _ else _)=_
   split; swap; · rfl
   have h : s.val=(Pair.fst s).val.disjSum (Pair.snd s).val := (congr_arg Subtype.val (Pair.mk_read s)).symm
   rw (occs:=.pos [1]) [h,Finset.prod_disjSum]

theorem layers [Fintype V][DecidableEq A][Fintype A] (o : A→V)(μ : (T→ℂ)→ₗ[ℂ]ℂ) (hμ : μ 1=1)
    {D : V⊕Multi.Hot (full A)→Type}[∀ i,Fintype (D i)](s : (together R (Lines A)).Mode)
    (f : ∀ i,D i → T → ℂ)(g : V⊕Multi.Hot (full A)→ T→ℂ)(H : ∀ i∈s.val, g i=∑ j:D i,f i j) :
    (connected (rises o g μ)).part s = ∑ z : ∀ i : (↑s.val),D i.val,
       (connected (rises o (fun i => if h : i∈s.val then f i (z ⟨i,h⟩) else g i) μ)).part s := by
   let W := fun x : V⊕Multi.Hot (full A)→ T→ℂ => (connected (rises o x μ)).part s
   apply picked s.val g f W
   intro i hi y
   have hu G : (rises (R:=R) o G μ).part (together R (Lines A)).quiet=1 := terms_quiet o _ _ hμ
   apply Marks.piece (hu _) univ (fun j => rises o (update y i (f i j)) μ) (fun _ _ => hu _) i s hi
   · intro t _ hv
     simp_rw [rises_part]; split
     next h =>
       have hy (a : T→ℂ) : ∏ j∈t.val,update y i a j=a*∏ j∈t.val.erase i,y j := by
          rw [← mul_prod_erase _ _ hv, Function.update_self]; congr 1
          exact prod_congr rfl fun j hj => update_of_ne (mem_erase.mp hj).1 ..
       simp_rw [hy,H i hi,sum_mul,map_sum];
     simp
   intro t _ hv j _; rw [rises_part,rises_part]; split; swap; · rfl
   congr 1; exact prod_congr rfl fun k hk => by simp [Function.update_of_ne (ne_of_mem_of_not_mem hk hv)]

end YM.RG02.Wick
