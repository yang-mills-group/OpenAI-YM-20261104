import YM.OPE.Compatible.Vines.Figure
/-! # Exact off-shell sword scaled grade. Slightly larger page grade allowance may include null. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp
open scoped Topology BigOperators Classical
variable {r d m n:ℕ}{c:ℝ}{W:Type*}{G:Gauge}
namespace Script
open Page
abbrev Alphabet (G:Gauge) (d:ℕ):=(j: Fin d)→Taylor G j.val
abbrev monoX {d:ℕ}(a:Fin d)(t: Taylor G a.val): Alphabet G d:=Pi.single a t
abbrev rankX {n d:ℕ}(k:Fin n→ Fin d):ℕ:= ∑ i,((k i).val+1)
abbrev spray (g:G.El)(p: Alphabet G d): Alphabet G d:= fun j=>Taylor.paint g (p j)
abbrev Chord (G:Gauge)(d r:ℕ):=MultilinearMap ℝ (fun _:Fin r=> Alphabet G d) ℝ
lemma fieldsX (v: Alphabet G d): ∑ i:Fin d, monoX i (v i)=v := by
     ext1 i; simp only [monoX, Finset.sum_apply]; rw [sum_eq_single i]
     · rw [Pi.single_eq_same]
     · intro j _ hj; exact Pi.single_eq_of_ne (Ne.symm hj) _
     simp
lemma deckSum (A:Chord G d r)(x:Fin r→ Alphabet G d): A x=∑ i:Fin r→ Fin d,A fun j=>monoX (i j) (x j (i j)):=by
    nth_rw 1 [show x=(fun j=>∑ i:Fin d, monoX i (x j i)) from funext fun i=> (fieldsX _).symm]; rw [MultilinearMap.map_sum_finset]; simp only [Fintype.piFinset_univ]
lemma spray_one (g:G.El)(t:Fin d)(j:Taylor G t.val): spray g (monoX t j)=monoX t (Taylor.paint g j):=by
    ext1 i; by_cases h:i=t
    · subst i; simp [spray,monoX]
    unfold spray monoX; rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h,_root_.map_zero]
structure Off (G:Gauge) (r n d:ℕ)(A: Chord G d r): Prop where
    Perms : ∀ x:Fin r→Alphabet G d,∀ t:Equiv.Perm (Fin r),A (x ∘ t)=A x
    Colors (g:G.El)(x:Fin r→ Alphabet G d) : A (fun i=>spray g (x i))=A x
    Grades (x: Fin r→ Fin d) (p:∀ i: Fin r,Taylor G (x i).val) : rankX x ≠ n → A (fun i=>monoX (x i) (p i))=0
def partX (G:Gauge)(r n d:ℕ):Submodule ℝ (Chord G d r) where
    carrier:=setOf (Off G r n d)
    zero_mem':=⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
    add_mem':=fun {v w} (h:Off G _ _ _ v) (he:Off G _ _ _ w)=> ⟨fun x a=>by simp only [add_apply,h.Perms x a,he.Perms x a],fun g u=>by simp only [add_apply, h.Colors,he.Colors],fun x p hp=>by simp [h.Grades x p hp,he.Grades x p hp]⟩
    smul_mem':=fun c A (h:Off G _ _ _ A)=> ⟨fun x s=>by simp only [smul_apply,h.Perms x s],fun g u=>by simp only [smul_apply,h.Colors],fun x p hp=> by simp [h.Grades x p hp]⟩
lemma part_unique (A B:partX G r n d)(h:∀ j:Fin r→ Fin d,rankX j=n→∀ z:Fin r→Alphabet G d,A.val (fun i=>monoX (j i) (z i (j i)))=B.val (fun i=>monoX (j i) (z i (j i)))):A=B:=by
    apply Subtype.ext; apply MultilinearMap.ext; intro x; rw [deckSum A.val,deckSum B.val]; apply sum_congr rfl fun i _=>?_; by_cases he:rankX i=n; exact h i he _
    exact ((show Off G r n d A.val from A.property).Grades i _ he).trans ((show Off G r n d B.val from B.property).Grades i _ he).symm
end Script
end YM.OPE.Flume
