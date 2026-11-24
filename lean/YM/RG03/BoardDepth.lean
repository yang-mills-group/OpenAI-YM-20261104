import YM.RG03.BoardStep

/-!
# Iterate path canonicalization through finite extra grades

Counts labels *as they occur* (allow duplicates, no cancellations needed). Both the depth and
length bound of intermediate paths matter. At fixed grades and depth the cost count and all
length ceilings are polynomial in input paths, not an exponential price per swap. The extra tail
is of actual polynomial products on the full group, not an equality asserted only in a formal
ring of jets. The gauge coefficient T and common anchor/color frame stay exactly the same; no
commutation of independent mask decisions follows from the additive identity alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Boards
open RG Wilson Lattice PathWords Finset Function
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{E:Type*}[AddCommMonoid E][Module ℝ E]
   {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private lemma sequence (T:Token G E ι)(o:Site n)(X:List (Board ι))(P Q:Board ι → Prop)(C:ℕ)
    (h:∀ x∈X,∃ (a b : List (Board ι)), a.length+b.length ≤ C ∧ (∀ i∈a,P i) ∧ (∀ i∈b,Q i) ∧
      ∀ U : Config G n, price T x o U=render T a o U+render T b o U) :
    ∃ (a b : List (Board ι)), a.length+b.length≤X.length*C ∧ (∀ i∈a,P i) ∧ (∀ i∈b,Q i) ∧
      ∀ U : Config G n, render T X o U=render T a o U+render T b o U := by
  induction X with
  | nil => exact ⟨[],[],by simp,by simp,by simp,by simp⟩
  | cons x y ih =>
    obtain ⟨a,b,hL,ha,hb,hc⟩:=h x List.mem_cons_self
    obtain ⟨c,d,hM,hc',hd',hr⟩:=ih (fun i hi => h i (List.mem_cons_of_mem x hi))
    refine ⟨a++c,b++d,by rw [List.length_append,List.length_append,List.length_cons,add_mul,one_mul];omega,fun i hi => (List.mem_append.mp hi).elim (ha i) (hc' i),fun i hi=>(List.mem_append.mp hi).elim (hb i) (hd' i),?_⟩
    intro U; rw [render_cons,hc,hr,render_append,render_append]; ac_rfl

def canonical (r:Board ι) := ∀ i, ∀ c ∈ r i, canon c=c
lemma chart_idem (w:Lattice.Walk) : chart (chart w)=chart w := by rw [chart,show Lattice.stop (0:Cover) (chart w)=Lattice.stop 0 w from route_end ..]; rfl
lemma canon_idem (c:Circuit) : canon (canon c)=canon c := congr_arg (fun v=> Circuit.mk v c.a c.b) (chart_idem c.prefix')
omit [Fintype ι] [DecidableEq ι] in
lemma straight_canon (r:Board ι) : canonical (straighten r) := by
  intro i c hc
  obtain ⟨v,-,rfl⟩:=List.mem_map.mp hc; exact canon_idem _

def bounded (L K : ℕ) (r:Board ι) := grade r ≤ K ∧ radius r L

def capacity (ι : Type*)[Fintype ι] (d L K : ℕ) := (1+rate (Fintype.card ι) L K)^d

theorem normalize_aux (T:Token G E ι)(o:Site n){l L K:ℕ}(r:Board ι) (d:ℕ) (hr:radius r l)
   (hL:l*3^d≤L)(hK:grade r+2*d≤K) : ∃ (X Y : List (Board ι)), X.length+Y.length ≤ capacity ι d L K ∧
       (∀ i∈X, canonical i ∧ grade r≤grade i ∧ bounded L K i) ∧
       (∀ i∈Y, grade r+d≤grade i ∧ bounded L K i) ∧
       ∀ U:Config G n, price T r o U=render T X o U+render T Y o U := by
  induction d generalizing r l with
  | zero =>
    rw [pow_zero,mul_one] at hL
    simp only [mul_zero,add_zero] at hK
    refine ⟨[],[r],by simp [capacity],by simp,(by
      intro x hx
      rw [show x=r from by simpa using hx]; exact ⟨Nat.le_refl _,hK,fun i=>(hr i).more hL⟩),by simp⟩
  | succ d ih =>
    obtain ⟨X,hX,hC,hU⟩:= step_canon T o r hr
    have hl' : (3*l)*3^d≤L := Eq.trans_le (by rw [Nat.pow_succ]; ac_rfl) hL
    have hz' : 3*l≤L := by nlinarith [one_le_pow₀ (a:=(3:ℕ)) (n:=d) (by decide)]
    have hz : l≤L := le_trans (by omega) hz'
    let A := fun i : Board ι=>canonical i ∧ grade r≤grade i ∧ bounded L K i
    let B := fun i : Board ι=>grade r+(d+1)≤grade i ∧ bounded L K i
    let C:= capacity ι d L K
    have hv x (hx:x∈X) : ∃ (a b : List (Board ι)), a.length+b.length ≤ C ∧ (∀ i∈a,A i) ∧ (∀ i∈b,B i) ∧
             ∀ U, price T x o U=render T a o U+render T b o U := by
      obtain ⟨ha,hb,hR⟩:=hC x hx
      obtain ⟨Y,Z,hP,hY,hZ,he'⟩:=ih (r:=x) (l:=3*l) hR hl' (by omega)
      refine ⟨Y,Z,hP,fun i hi=>?_,fun i hi=>?_,he'⟩
      · obtain ⟨h,h',h''⟩:=hY i hi; exact ⟨h,by omega,h''⟩
      obtain ⟨h,h'⟩:=hZ i hi; exact ⟨by omega,h'⟩
    obtain ⟨Y,Z,hm,hY,hZ,hV⟩ := sequence T o X A B C hv
    refine ⟨straighten r::Y,Z,?_,?_,hZ,fun U=>by rw [render_cons,hU,hV]; exact (add_assoc ..).symm⟩
    · let C:=rate (Fintype.card ι) L K
      have ht : X.length ≤ C := hX.trans (by
        dsimp only [C,rate]
        have : grade r≤K:=by omega
        gcongr)
      simp only [List.length_cons, capacity, pow_succ] at hm ⊢
      change _ ≤ X.length*(1+C)^d at hm
      calc
        _ = Y.length+Z.length+1 := by omega
        _ ≤ C*(1+C)^d+(1+C)^d := Nat.add_le_add (hm.trans (Nat.mul_le_mul_right _ ht)) (one_le_pow₀ (by omega))
        _ = (1+C)^d*(1+C) := by ring
    intro x hx; rcases List.mem_cons.mp hx with he|he
    · rw [he]; refine ⟨straight_canon _,(aligned_parallel _).grade_eq.le,?_,fun i=>(hr.straighten i).more hz⟩
      rw [← (aligned_parallel r).grade_eq]
      omega
    exact hY x he

theorem normalize_words (T:Token G E ι)(o:Site n)(l:ℕ)(r:Board ι) (d:ℕ) (hr:radius r l) :
    let L:=l*3^d
    let K:=grade r+2*d
    ∃ (X Y : List (Board ι)), X.length+Y.length ≤ capacity ι d L K ∧
       (∀ i∈X, canonical i ∧ grade r≤grade i ∧ bounded L K i) ∧
       (∀ i∈Y, grade r+d≤grade i ∧ bounded L K i) ∧
       ∀ U:Config G n, price T r o U=render T X o U+render T Y o U :=
  normalize_aux T o r d hr (le_refl _) (le_refl _)
end YM.RG03.Boards
