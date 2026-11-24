import Mathlib

/-!
# Slotwise polynomial frame action on tested amplitudes

No formal continuum limit is assumed. Used for finite X-space
normalization tests in fixed coordinate labels (unnormalized readings first).
Insertion/lab normalization maps are applied in each separate slot, not as a
connected-only projection.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace YM.PertExtension.Position
open Set Function Filter PowerSeries
open scoped Topology BigOperators Classical
variable (J : Type*) [Fintype J]{P : Type*}(arity : P→ℕ)

abbrev Mark := (s:P) × (Fin (arity s)→J)
abbrev FrameAt (J : Type*) (R : Type*) := J→J→R

def insert {R : Type*}[CommSemiring R] (a : Mark J arity→R)(k:FrameAt J R)(v : Mark J arity) : R :=
  ∑ w:Fin (arity v.1)→J, a ⟨v.1,w⟩*∏ i, k (v.2 i) (w i)

variable {J arity}
lemma insert_congr {R}[CommSemiring R] {a b:Mark J arity→R} (k:FrameAt J R) (v:Mark J arity) (hab : ∀ w,a ⟨v.1,w⟩=b ⟨v.1,w⟩) :
    insert J arity a k v=insert J arity b k v :=
  Finset.sum_congr rfl fun w _=>congr_arg (fun c=>c*_) (hab w)
lemma insert_one {R}[CommSemiring R] (a : Mark J arity→R)(v:Mark J arity) :
    insert J arity a (fun i j=> if i=j then (1:R) else 0) v=a v := by
  unfold insert; rw [Finset.sum_eq_single_of_mem v.2 (by simp) (fun i hi hh=>?_)]
  · simp
  obtain ⟨j,hj⟩:=not_forall.mp ((mt funext) hh)
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (Ne.symm hj))]
  simp

lemma insert_twice {R}[CommSemiring R](a: Mark J arity→R)(k l : FrameAt J R) :
    insert J arity (insert J arity a k) l = insert J arity a (fun i j=> ∑ h,l i h*k h j) := by
   funext v
   unfold insert
   simp only [Finset.sum_mul]
   apply (Finset.sum_comm (f:=fun (u w : Fin (arity v.1)→J) =>
       ((a ⟨v.1,w⟩ * ∏ i,k (u i) (w i)) * ∏ i,l (v.2 i) (u i))) (s:=Finset.univ) (t:=Finset.univ)).trans
   apply Finset.sum_congr rfl
   intro w hw
   rw [Finset.prod_univ_sum (fun i:Fin (arity v.1)=>Finset.univ) (fun i j=>l (v.2 i) j*k j (w i)), Finset.mul_sum]
   refine Finset.sum_congr rfl fun u hu=>?_
   rw [Finset.prod_mul_distrib]
   ring

section series
variable {R : Type*}[CommRing R]
lemma insert_constant (a : Mark J arity→R⟦X⟧)(k : FrameAt J R⟦X⟧)(v:Mark J arity) :
    (insert J arity a k v).constantCoeff = insert J arity (fun w=> (a w).constantCoeff) (fun i j=>(k i j).constantCoeff) v := by
  simp [insert,map_sum,map_prod]
lemma insert_alg {S : Type*}[CommRing S](φ : R →+* S)(a : Mark J arity→R)(k)(v) :
    φ (insert J arity a k v)= insert J arity (fun w=> φ (a w)) (fun i j=>φ (k i j)) v:= by simp [insert,map_sum,map_prod]

/-- Agreement in *one* strictly positive coefficient as linearized first variation.
Used with common coefficients below that degree. -/
structure Strike (n : ℕ) (p p' : R⟦X⟧)(c : R) : Prop where
   lower : ∀ i<n, coeff i p=coeff i p'
   value : coeff n p+c=coeff n p'

namespace Strike
variable {n : ℕ}{p p' q q' : R⟦X⟧}{c d : R}
theorem same (p:R⟦X⟧): Strike n p p 0:=⟨fun _ _=>rfl,add_zero _⟩

private lemma mul_help (h : ∀ i≤n, coeff i p=coeff i p')(u : ∀ i≤n, coeff i q=coeff i q') :
    coeff n (p*q)=coeff n (p'*q') := by
    simp_rw [coeff_mul]; exact Finset.sum_congr rfl (fun (i : ℕ×ℕ) hi=>by rw [h _ (by obtain he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi;omega), u _ (by obtain he := Finset.HasAntidiagonal.mem_antidiagonal.mp hi;omega)])

theorem mul (hN : 0<n)(h : Strike n p p' c)(u : Strike n q q' d) : Strike n (p*q) (p'*q') (c*constantCoeff q+constantCoeff p*d) := by
   simp_rw [← coeff_zero_eq_constantCoeff_apply]
   constructor
   · intro i hi; exact mul_help (fun j h'=>h.lower _ (h'.trans_lt hi)) (fun j h'=>u.lower _ (h'.trans_lt hi))
   let A := Finset.HasAntidiagonal.antidiagonal n
   let B := A.erase (0,n)
   let O := B.erase (n,0)
   have he (x y:R⟦X⟧) :
      coeff n (x*y)=coeff n x * coeff 0 y + coeff 0 x * coeff n y +
        ∑ a∈O,coeff a.1 x * coeff a.2 y := by
      let F := fun a:ℕ×ℕ=> coeff a.1 x * coeff a.2 y
      have h₁ : F (0,n)+(∑ a∈B, F a) = ∑ a∈A, F a:=Finset.add_sum_erase A F (a:=(0,n)) (by simp [A])
      have h₂ : F (n,0)+(∑ a∈O,F a)=∑ a∈B,F a:= Finset.add_sum_erase B F (a:=(n,0)) (by simp [A,B,hN.ne'])
      rw [coeff_mul];change ∑ a∈A,F a=F (n,0)+F (0,n)+∑a∈O,F a
      rw [←h₁,←h₂]
      abel
   rw [he,he,← h.value,←u.value,h.lower 0 hN,u.lower 0 hN]
   have hh : (∑ a∈O,coeff a.1 p * coeff a.2 q)=∑ a∈O,coeff a.1 p' * coeff a.2 q' := by
      refine Finset.sum_congr rfl ?_;rintro ⟨i,j⟩ hi
      simp only [O,B,A,Finset.mem_erase,ne_eq,Prod.mk.injEq,Finset.HasAntidiagonal.mem_antidiagonal] at hi
      rw [h.lower _ (by omega), u.lower _ (by omega)]
   rw [hh]; ring
theorem add (h : Strike n p p' c)(u : Strike n q q' d) : Strike n (p+q) (p'+q') (c+d) := by
  constructor
  · exact fun j hj=>by rw [map_add,map_add,h.lower _ hj,u.lower _ hj]
  rw [map_add,map_add,←h.value,← u.value];ring

theorem smul (h : Strike n p p' c)(x:R) : Strike n (C x*p) (C x*p') (x*c):= by
  constructor
  · intro i hi;rw [coeff_C_mul,coeff_C_mul,h.lower _ hi]
  rw [coeff_C_mul,coeff_C_mul,←h.value, mul_add]

theorem sum {ι : Type*}{f g : ι→PowerSeries R}{v : ι→R} (s : Finset ι)(h : ∀i∈s,Strike n (f i) (g i) (v i)) :Strike n (∑ i∈s,f i) (∑ i∈s,g i) (∑ i∈s,v i):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simp [same]
  | insert j s hj ih=>simpa [hj] using (h j (by simp)).add (ih (fun i hi=>h i (by simp [hi])))

lemma evaluation {f g : FrameAt J R⟦X⟧}{u : FrameAt J R}{a:Mark J arity→R⟦X⟧}{v : Mark J arity} (hn:0<n)(h:∀ i j,Strike n (f i j) (g i j) (u i j)) :
  Strike n (insert J arity a f v) (insert J arity a g v) (coeff 1 (insert J arity (fun w=> PowerSeries.C ((a w).constantCoeff))
    (fun i j=> PowerSeries.C ((f i j).constantCoeff)+PowerSeries.C (u i j) * PowerSeries.X) v)):=by
   have h'1 (i j) : Strike 1 (PowerSeries.C ((f i j).constantCoeff))
       (PowerSeries.C ((f i j).constantCoeff)+PowerSeries.C (u i j) * PowerSeries.X) (u i j):= by
      constructor
      · intro d hd; interval_cases d
        simp
      simp
   have h₁ (w : Fin (arity v.1)→J)(s:Finset (Fin (arity v.1))) : ∃ c : R,
      Strike n (∏ i∈s,f (v.2 i) (w i)) (∏ i∈s,g (v.2 i) (w i)) c ∧
      Strike 1 (∏ i∈s,PowerSeries.C ((f (v.2 i) (w i)).constantCoeff))
       (∏ i∈s,(PowerSeries.C ((f (v.2 i) (w i)).constantCoeff)+PowerSeries.C (u (v.2 i) (w i)) * PowerSeries.X)) c := by
      induction s using Finset.induction_on with
      | empty=>exact ⟨0,(by simpa using same _),(by simpa using same _)⟩
      | insert i s he ih=>
        obtain ⟨d,H,h'⟩:=ih;
        let vf j:= f (v.2 j) (w j); let vg j:= g (v.2 j) (w j); let vu j:= u (v.2 j) (w j)
        have hv : Strike n (vf i) (vg i) (vu i) := h _ _
        have ha := hv.mul hn H; have ha' := (h'1 (v.snd i) (w i)).mul (by omega) h'
        simp only [Finset.prod_insert he, map_prod, constantCoeff_C] at ha ha' ⊢
        exact ⟨_,ha,ha'⟩
   choose d ha₁ ha₂ using fun w=>h₁ w Finset.univ
   have ht := Strike.sum (n:=n) Finset.univ (fun w _=>(Strike.same (a ⟨v.1,w⟩)).mul hn (ha₁ w))
   have ht' := Strike.sum (n:=1) Finset.univ (fun w _=>(Strike.same (PowerSeries.C (a ⟨v.1,w⟩).constantCoeff)).mul one_pos (ha₂ w))
   simp only [zero_mul,zero_add,constantCoeff_C] at ht ht'
   have hc (v:Mark J arity): (∑ w:Fin (arity v.1)→J, PowerSeries.C ((a ⟨v.1,w⟩).constantCoeff) * ∏ i,PowerSeries.C ((f (v.2 i) (w i)).constantCoeff)) = PowerSeries.C
        (∑ w:Fin (arity v.1)→J, (a ⟨v.1,w⟩).constantCoeff * ∏ i,(f (v.2 i) (w i)).constantCoeff) := by simp only [map_prod,map_sum,map_mul]
   have he := ht'.value
   unfold insert
   rw [hc,coeff_C,if_neg (by decide),zero_add] at he
   exact he ▸ ht
end Strike

end series
end YM.PertExtension.Position
