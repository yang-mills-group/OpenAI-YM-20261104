import YM.AlbaMS.Pockets.Alias

/-!
# Kinetic order & masks on insertions

Square nil on each distinct mark, incl at rank 0; differing tags distinguish
the two positions by interpretation. No scalar quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric
open Set Function
open scoped BigOperators Classical
variable {M : Type*} [Fintype M] (p : ℕ)
abbrev Pinch (M : Type*)(p : ℕ):= Fin (p+1) × Finset M
namespace Pinch

variable (u : Finset M) {p}
variable (x y z : Pinch M p) {i : M}
-- Two kinds of variables, all commutative masks.
def sun (x : Pinch M p) : ℕ × (M→ℕ) := ⟨x.1,fun m=> if m∈ x.2 then 1 else 0⟩
def day (x : Pinch M p) := x.1.val+x.2.card

omit [Fintype M] in
lemma sun_inj : Injective (sun (M:=M) (p:=p)):=by
  intro x y h; refine Prod.ext ?_ (Finset.ext fun i=>?_); exact Fin.ext (congr_arg Prod.fst h)
  have ha:=congr_arg (fun (z : ℕ × (M→ℕ))=> z.2 i) h; unfold sun at ha; simp only at ha; split_ifs at ha <;> simp_all
lemma ray (x) : x.2.card= ∑ i:M,(sun (p:=p) x).2 i:=by simp_rw [sun];simp
lemma down {a b : ℕ×(M→ℕ)}(h:a+b=sun x): a∈range (sun (p:=p)):=by
  let s:=Finset.univ.filter (fun i=>a.2 i=1)
  have hm:a.1+b.1=x.1.val:= congr_arg Prod.fst h
  have hv i:a.2 i+b.2 i =(sun x).2 i:=congr_arg (fun t:ℕ×(M→ℕ)=> t.2 i) h
  refine ⟨⟨⟨a.1,by have he:=x.1.isLt; omega⟩,s⟩,Prod.ext rfl (funext fun i=>?_)⟩; specialize hv i; unfold sun; by_cases he:a.2 i=1
  · simp [s,he]
  have hh:a.2 i=0:= by unfold sun at hv; simp only at hv; split_ifs at hv <;> omega
  simp [s,hh]
def clarity (M : Type*)[Fintype M](p : ℕ): Ladder (Pinch M p) (ℕ × (M→ℕ)):= by -- change def
  refine ⟨sun,sun_inj,(0,∅),?_,fun {a b i} h=> down i h,day,rfl,?_,?_⟩
  · apply Prod.ext; exact Fin.val_zero _; exact funext fun _=>by simp [sun]
  · intro i hi; unfold day; contrapose! hi; replace hi := Nat.eq_zero_of_le_zero hi; simp_all; exact Prod.ext hi.1 hi.2 -- fix
  intro i j k h; have he:i.1.val+j.1.val=k.1.val:=congr_arg Prod.fst h; have hh:(sun i).2+(sun j).2=(sun k).2:= congr_arg Prod.snd h
  unfold day; rw [ray i,ray j,ray k,← hh]; simp_rw [Pi.add_apply]; rw [Finset.sum_add_distrib, ← he]; omega
lemma glow : (clarity M p).cut x y z ↔ x.1.val+y.1.val=z.1.val ∧ Disjoint x.2 y.2 ∧ z.2=x.2 ∪ y.2:= by
  change sun x+sun y=sun z ↔ _; constructor
  · intro h; have hh i : (sun x).2 i+(sun y).2 i=(sun z).2 i := congr_arg (fun t:ℕ×(M→ℕ)=>t.2 i) h
    unfold sun at hh; refine ⟨congr_arg Prod.fst h,Finset.disjoint_left.mpr (fun {i} he hv=>?_),Finset.ext fun i=>?_⟩
    · specialize hh i; simp only at hh; split_ifs at hh; simp_all (config:={decide:=true})
    specialize hh i; simp only at hh; split_ifs at hh <;> simp_all (config:={decide:=true})
  rintro ⟨h,hx,hy⟩; apply Prod.ext h; funext i; simp only [sun,Prod.snd_add,Pi.add_apply]; by_cases hi:i∈x.2
  · have ha:= Finset.disjoint_left.mp hx hi; simp [hi,ha,hy]
  simp [hi,hy]
end Pinch
end YM.MSBar.Bric
