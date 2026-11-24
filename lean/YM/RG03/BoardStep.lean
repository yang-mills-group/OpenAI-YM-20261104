import YM.RG03.PathWords

/-!
# Aligned word bundles, one grade at a time

Retain one color multilinear coefficient on a bundle of words (one for each original multilinear
slot). Additional polynomial products may appear *inside* a slot. Therefore the output can still
retain invariance for simultaneous conjugation at the root, which would be problematic if splitting
one contraction into individual basis components as labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Boards
open RG Wilson Lattice PathWords Finset Function
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{E:Type*}[AddCommMonoid E][Module ℝ E]
   {ι:Type*}

abbrev Board (ι : Type*) := ι→Word
abbrev Token (G:Gauge) (E:Type*) [AddCommMonoid E][Module ℝ E] (ι:Type*) :=
  MultilinearMap ℝ (fun _ : ι => G.Mat) E

def grade [Fintype ι] (r:Board ι) : ℕ := ∑ i, (r i).length
def radius (r:Board ι) (l:ℕ) := ∀ i, short (r i) l
def parallel (r s:Board ι) : Prop := ∀ i, paired (r i) (s i)

def chart (w:Walk) := route (0:Cover) (stop 0 w) 1
def canon (c:Circuit) := { c with prefix':=chart c.prefix' }
def straighten (r:Board ι) : Board ι := fun i => (r i).map canon

def arrayValue (r:Board ι) (o:Site n)(U:Config G n) := fun i=>value (r i) o U
def price (T:Token G E ι) (r:Board ι) (o:Site n)(U:Config G n) : E := T (arrayValue r o U)
def render (T:Token G E ι) (r:List (Board ι)) (o:Site n) (U:Config G n) : E := (r.map fun p=>price T p o U).sum

@[simp] lemma render_nil (T:Token G E ι)(o:Site n) (U:Config G n) : render T [] o U=0 := rfl
@[simp] lemma render_cons (T:Token G E ι)(a:Board ι)(b:List (Board ι))(o:Site n) (U:Config G n) : render T (a::b) o U=price T a o U+render T b o U := rfl
@[simp] lemma render_append (T:Token G E ι)(a b : List (Board ι))(o:Site n) (U:Config G n) : render T (a++b) o U=render T a o U+render T b o U := by simp [render]

-- Length estimate (same axis route convention as e.g. YM.Push.PriceCompiler.Canonical, without
-- importing its kernel price inputs).
private def taxi (x:Cover):ℕ :=∑ i, (x i).natAbs
private lemma taxi_step (c:Step) : taxi (c.vec:Cover)=1 := by
  rcases c with ⟨a,b|b⟩
  · change taxi (step (S:=ℤ) a)=_
    simp [taxi,step_apply,apply_ite (fun x : ℤ=> x.natAbs)]
  change taxi (-(step (S:=ℤ) a))=_
  simp [taxi,step_apply,apply_ite (fun x : ℤ=> x.natAbs)]
private lemma taxi_add (x y : Cover): taxi (x+y) ≤ taxi x+taxi y := by
  unfold taxi; rw [← Finset.sum_add_distrib]; exact sum_le_sum (fun i _=> Int.natAbs_add_le (x i) (y i))
private lemma taxi_end (x:Cover)(w:Walk) : taxi (stop x w) ≤ taxi x+w.length := by
  induction w generalizing x with
  | nil => rfl
  | cons a b ih =>
    have h:= ih (x+a.vec); have hs:=taxi_add x a.vec; rw [taxi_step] at hs
    rw [stop,List.length_cons]; omega
lemma chart_length (w:Walk) : (chart w).length ≤ w.length := by
  have he : allAxes 1 = [0,1,2,3] := by decide
  have hs := taxi_end 0 w; rw [show taxi 0=0 by simp [taxi],zero_add] at hs
  rw [show (chart w).length=taxi (stop 0 w) from (by simp [chart,route,axisRoute,he,taxi,Fin.sum_univ_succ,straight,Axis])]
  exact hs
lemma paired_map (w:Word) : paired w (w.map canon) := by
  induction w with
  | nil => exact List.Forall₂.nil
  | cons a w ih => exact List.Forall₂.cons (show similar a (canon a) from ⟨rfl,rfl,(route_end ..).symm⟩) ih
lemma parallel.grade_eq [Fintype ι] {r s:Board ι} (h:parallel r s) : grade r=grade s := sum_congr rfl (fun i _=> (h i).length_eq)
lemma radius.straighten {r:Board ι}{l:ℕ}(hr:radius r l) : radius (straighten r) l :=
  fun i _ hz => let ⟨v,hv,he⟩:=List.mem_map.mp hz;(congr_arg (·.prefix'.length) he.symm).le.trans ((chart_length _).trans (hr i v hv))
lemma aligned_parallel (r:Board ι) : parallel r (straighten r) := fun i => paired_map (r i)

variable [DecidableEq ι]

lemma array_updated (r:Board ι) (i:ι) (w:Word)(o:Site n)(U:Config G n) :
    arrayValue (update r i w) o U = update (arrayValue r o U) i (value w o U) := by
  funext j; by_cases he : j=i
  · subst j; simp [arrayValue]
  rw [update_of_ne he]; unfold arrayValue; rw [update_of_ne he]

lemma price_update (T:Token G E ι) (r:Board ι) (i:ι) (X:List Word)(o:Site n)(U:Config G n) :
    T (update (arrayValue r o U) i (total X o U))=render T (X.map (update r i)) o U := by
  induction X with
  | nil => simp
  | cons x a ih => rw [total_cons,T.map_update_add,ih,List.map_cons,render_cons,price,array_updated]

theorem replace_leg (T:Token G E ι) (r:Board ι) (i:ι) (w:Word)(X:List Word)(o:Site n)(U:Config G n)
    (h : value (r i) o U=value w o U+total X o U) :
    price T r o U=price T (update r i w) o U+render T (X.map (update r i)) o U := by
  rw [price,price,← update_eq_self i (arrayValue r o U),show arrayValue r o U i=value (r i) o U from rfl, h,T.map_update_add,array_updated]
  rw [price_update]

variable [Fintype ι]
lemma grade_update (r:Board ι) (i:ι) (w:Word) :
    grade (update r i w) + (r i).length = grade r + w.length := by
  have hh (p:Board ι) := Finset.add_sum_erase Finset.univ (fun j=> (p j).length) (mem_univ i)
  unfold grade; rw [← hh (update r i w),← hh r,update_self]
  have he j (hj : j∈ univ.erase i) : (update r i w j).length=(r j).length :=by apply congr_arg; apply update_of_ne; exact (mem_erase.mp hj).1
  rw [sum_congr rfl (show ∀ j∈univ.erase i, (fun j=> (update r i w j).length) j = (fun j=> (r j).length) j from he)]
  ac_rfl

/-- Over-count using total number of slots instead of branching at every unused slot; compatible with
fixed marker load. -/
def rate (d l K:ℕ):ℕ := d*(12*l^2*K)

private lemma step_aux (T:Token G E ι)(o:Site n)(Q:Finset ι)(r s:Board ι){l K:ℕ}
    (hp:parallel r s)(hr:radius r l)(hs:radius s l)(hK:grade r ≤ K)(hmain:∀i∉Q, r i=s i) : ∃ X : List (Board ι), X.length ≤ rate Q.card l K ∧
      (∀ b∈X, grade r+1 ≤ grade b ∧ grade b ≤ grade r+2 ∧ radius b (3*l)) ∧
       ∀ U : Config G n, price T r o U=price T s o U+render T X o U := by
  induction Q using Finset.induction_on generalizing r with
  | empty => refine ⟨[],by simp [rate],by simp, fun _=>by rw [show r=s from funext fun i=>hmain i (notMem_empty _),render_nil,add_zero]⟩
  | @insert i q hi ih =>
    obtain ⟨X,hX,hL,hU⟩:= PathWords.lift_words G o _ _ (hp i) (hr i) (hs i)
    let r' := update r i (s i)
    have hp' : parallel r' s:= by
      intro j; by_cases he : j=i
      · subst j; unfold r'; rw [update_self]; change List.Forall₂ similar (s i) _; induction s i with | nil => exact List.Forall₂.nil | cons c t ih => exact List.Forall₂.cons (R:=similar) ⟨rfl,rfl,rfl⟩ ih
      unfold r'; rw [update_of_ne he]; exact hp j
    have hr' : radius r' l := by
      intro j; by_cases he : j=i
      · subst j; simpa [r'] using hs i
      unfold r'; rw [update_of_ne he]; exact hr j
    have hge : grade r'=grade r:=hp'.grade_eq.trans hp.grade_eq.symm
    obtain ⟨Y,hM,hY,hV⟩ := ih r' hp' hr' (hge ▸ hK) (fun c hc=> (eq_or_ne c i).elim (fun he=>by subst c; simp [r']) (fun he=>(update_of_ne he ..).trans (hmain c (by simpa using And.intro he hc))))
    refine ⟨X.map (update r i)++Y, ?_, fun b hb=>?_,fun U=>by rw [render_append,replace_leg T r i (s i) X o U (hU U),← show r'=update r i (s i) from rfl,hV]; ac_rfl⟩
    · have he : (r i).length ≤ grade r:=show List.length (r i) ≤ ∑ j, List.length (r j) from single_le_sum (f:=fun j=>List.length (r j)) (fun _ _=>Nat.zero_le _) (mem_univ i)
      rw [List.length_append,List.length_map,card_insert_of_notMem hi]
      calc
        _ ≤ 12*l^2*K + rate q.card l K := add_le_add (hL.trans (Nat.mul_le_mul_left _ (he.trans hK))) hM
        _ = _ := by unfold rate; rw [add_mul,one_mul,add_comm]
    rcases List.mem_append.mp hb with hb|hb
    · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hb; obtain ⟨ha,hb,hZ⟩:= hX z hz
      have hgrade := grade_update r i z
      refine ⟨by omega,by omega,fun j=>?_⟩
      by_cases he : j=i
      · subst j; rw [update_self]; exact hZ
      rw [update_of_ne he]; exact (hr j).more (by omega)
    obtain ⟨he,hM,hR⟩:=hY b hb; rw [← hge]; exact ⟨he,hM,hR⟩

lemma step_all (T:Token G E ι)(o:Site n) (r s:Board ι){l:ℕ}
    (hp:parallel r s)(hr:radius r l)(hs:radius s l) : ∃ X : List (Board ι),
    X.length ≤ rate (Fintype.card ι) l (grade r) ∧
    (∀ b∈X, grade r+1 ≤ grade b ∧ grade b ≤ grade r+2 ∧ radius b (3*l)) ∧
    ∀ U : Config G n, price T r o U=price T s o U+render T X o U :=
  step_aux T o univ r s hp hr hs le_rfl (fun _ hi=>False.elim (hi (mem_univ _)))

/-- First lexicographic-level path pass. -/
theorem step_canon (T:Token G E ι)(o:Site n)(r:Board ι){l:ℕ}(hr:radius r l) : ∃ X : List (Board ι),
    X.length ≤ rate (Fintype.card ι) l (grade r) ∧
    (∀ b∈X, grade r+1 ≤ grade b ∧ grade b ≤ grade r+2 ∧ radius b (3*l)) ∧
    ∀ U : Config G n, price T r o U=price T (straighten r) o U+render T X o U :=
  step_all T o r (straighten r) (aligned_parallel r) hr hr.straighten
end YM.RG03.Boards
