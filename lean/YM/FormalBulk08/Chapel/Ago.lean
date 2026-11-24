import YM.FormalBulk08.Rift.Charge
import Mathlib.RingTheory.Binomial
/-! Discrete polynomial expansion, paths sym. No derivatives from operational
kinetics in ˋℝˊ directly. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Lattice Laurent Rift Gorge Function
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {A V E: Type*}[Fintype A][AddCommGroup E][Module ℝ E]

abbrev Wand (A:Type*):= A→ℤ
abbrev Grades (A:Type*):= A→ℕ
def buzz (i:A):Wand A:=fun j=> if j=i then 1 else 0
def grain (i:A):Grades A:=fun j=>if j=i then 1 else 0
def upper (t: Grades A):ℕ := ∑ i,t i
def booth (U : Wand A→ E)(a:A)(w : Wand A) := U (w+buzz a)-U w
def gang (U:Wand A→E) : List A → Wand A→E
   | []=>U
   | i::l=> booth (gang U l) i
omit [Fintype A] [Module ℝ E] in
lemma gang_booth (U: Wand A→E)(l:List A)(i:A): gang (booth U i) l=booth (gang U l) i := by
    induction l with
    | nil=>rfl
    | cons j l h=>rw [gang,gang,h];ext x;simp only [booth,add_right_comm x (buzz j)]; abel
omit [Fintype A] [Module ℝ E] in
lemma gangs (U : Wand A→E){l l':List A}(h:l.Perm l') : gang U l=gang U l':= by
   induction h with
   | nil=>rfl
   | cons a h ih=>rw [gang,gang,ih]
   | swap a b l => ext x; simp only [gang,booth, add_right_comm x (buzz b)];abel -- permutation notation
   | trans _ _ i j=>exact i.trans j

def store (t:Grades A): Multiset A:= ∑ i: A,Multiset.replicate (t i) i
def roll (t:Grades A): List A:= (store t).toList
lemma upper_push (t:Grades A)(a:A): upper (t+grain a)=upper t+1:=by simp [upper,grain,Finset.sum_add_distrib,Pi.add_apply]
lemma store_h (t:Grades A)(a:A): (store t).count a=t a := by
  unfold store;rw [Multiset.count_sum', Finset.sum_eq_single a]; all_goals simp
  intro b h hb; exact h (Multiset.eq_of_mem_replicate hb).symm
lemma merch (t:Grades A): (roll t).length=upper t:= by rw [roll,Multiset.length_toList,store,Multiset.card_sum]; simp [upper]
lemma tailor_ray (t:Grades A)(a:A): (roll (t+grain a)).Perm (a::roll t):= by
   rw [← Multiset.coe_eq_coe]; apply Multiset.ext.mpr;intro i; rw [←Multiset.cons_coe];simp only [roll,Multiset.coe_toList, store_h,Multiset.count_cons, grain,Pi.add_apply]

def hat (t:Grades A)(w:Wand A) : ℝ:= ∏ i: A, Ring.choose (w i: ℝ) (t i)
def trimmed (A : Type*)[Fintype A](r:ℕ) : Finset (Grades A):= (Finset.Icc 0 (fun _:A=>r)).filter (fun t=>upper t<r)
lemma trim_def (t:Grades A)(r:ℕ): t ∈ trimmed A r ↔ upper t <r := by
    refine ⟨fun h=>(Finset.mem_filter.mp h).2,fun h=> Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨fun i=>Nat.zero_le _,fun i=>?_⟩,h⟩⟩; exact (Finset.single_le_sum (f:=t) (fun k _=>Nat.zero_le _) (Finset.mem_univ i)).trans h.le
lemma hat_live (t:Grades A)(a:A)(w:Wand A): hat (t+grain a) (w+buzz a) - hat (t+grain a) w=hat t w:= by
    let S:=(Finset.univ:Finset A).erase a
    let F (t:Grades A)(w:Wand A) := ∏ i∈S,Ring.choose (w i:ℝ) (t i)
    have he t w: hat t w=Ring.choose (w a:ℝ) (t a)*F t w := (Finset.mul_prod_erase (Finset.univ:Finset A) _ (Finset.mem_univ _)).symm
    have hu:F (t+grain a) (w+buzz a)=F t w:=Finset.prod_congr rfl fun i hi=> by simp [grain,buzz,(Finset.mem_erase.mp hi).1]
    have hv:F (t+grain a) w=F t w:=Finset.prod_congr rfl fun i hi=> by simp [grain,(Finset.mem_erase.mp hi).1]
    rw [he,he,he,hu,hv, ←sub_mul]; simp [grain,buzz,Ring.choose_succ_succ]
lemma hat_dead (t:Grades A)(a:A)(h:t a=0)(w:Wand A):hat t (w+buzz a)=hat t w:= by
    unfold hat; refine Finset.prod_congr rfl fun i _=>?_; by_cases he:i=a
    · rw [he,h];simp
    simp [buzz,he]
lemma hat_origin (t:Grades A):hat t 0= if t=0 then 1 else 0:= by
    split_ifs with h
    · subst t;simp [hat]
    obtain ⟨a,h⟩:= Function.ne_iff.mp h; unfold hat; rw [Finset.prod_eq_zero (Finset.mem_univ a)]; simp only [Pi.zero_apply,Int.cast_zero]; exact Ring.choose_zero_pos ℝ (Nat.pos_of_ne_zero h) -- name

def party (r:ℕ)(U:Wand A→E)(w : Wand A):=∑ t∈ trimmed A r, hat t w • gang U (roll t) 0
lemma trim_nil : trimmed A 0=∅:= Finset.eq_empty_iff_forall_notMem.mpr (fun t=>by simp [trim_def])
lemma party_corner {r:ℕ}(h:0<r)(U:Wand A→E):party r U 0=U 0 := by unfold party;simp_rw [hat_origin];rw [Finset.sum_eq_single 0]; all_goals simp_all [trim_def,roll,store,upper, gang] -- perhaps
lemma party_game (r:ℕ)(U:Wand A→E)(i:A) : booth (party (r+1) U) i= party r (booth U i):= by
   funext w
   unfold booth party at * -- don't unfold both
   rw [← Finset.sum_sub_distrib]; symm; simp_rw [← sub_smul]
   let f (t:Grades A):=t+grain i
   let g (t:Grades A):= t-grain i
   let L:= trimmed A (r+1)
   have ht {t:Grades A}(h:t i≠0):f (g t)=t:= by ext k;by_cases he:k=i <;> simp [f,g,he,grain];omega
   -- RHS extend zero
   let S := (trimmed A r).image f
   rw [← Finset.sum_subset (s₁:=S) (s₂:=trimmed A (r+1)) (by rintro x hx; obtain ⟨z,hz,rfl⟩:= Finset.mem_image.mp hx; exact (trim_def ..).mpr (by unfold f;rw [upper_push]; have :=(trim_def ..).mp hz;omega)) ?h, Finset.sum_image]; swap;· exact (fun _ _ _ _ h=>add_right_cancel h)
   · apply Finset.sum_congr rfl;intro a _; unfold f; rw [hat_live, gangs U (tailor_ray ..),gang];congr 1; exact congr_fun (gang_booth U (roll a) i) _
   case h=>
      intro b hb hh; rw [hat_dead,sub_self,zero_smul]; by_contra hn; apply hh; refine Finset.mem_image.mpr ⟨g b,(trim_def ..).mpr ?_,ht hn⟩
      have he := (trim_def ..).mp hb
      have h := upper_push (g b) i; change upper (f (g b))= _ at h;rw [ht hn] at h; omega
end YM.FormalBulk08.Chapel
