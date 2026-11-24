import YM.SchemeConversionRG11.Maxwell.Corona

/-! # Complex null tests

Monic tail division and rank-one factor patching. No appeal to stabilizers of
an observable net or algebraic group schemes. In particular the base field is
specified on each chart.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Corona
open Function Filter Maxwell Set Complex MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace

def tailMap : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] Script := rename Fin.succ
lemma tail_at (p : MvPolynomial (Fin 3) ℂ) (x : Space) : aeval x (tailMap p)=aeval (fun i : Fin 3 ↦ x i.succ) p := by
  induction p using MvPolynomial.induction_on with
  | C => simp [tailMap]
  | add _ _ hx hy => rw [map_add,map_add,map_add,hx,hy]
  | mul_X q i h => rw [map_mul,map_mul,map_mul,h]; simp [tailMap]

def tailS : MvPolynomial (Fin 3) ℂ := ∑ i:Fin 3, X i^2
lemma chart_tail : chart=X 0^2+tailMap tailS := by
  unfold chart Axis tailMap tailS
  rw [Fin.sum_univ_succ]; simp

abbrev Remainders (p : Script) := ∃ (q : Script) (u v : MvPolynomial (Fin 3) ℂ),
  p = q*chart+tailMap u + X 0*tailMap v
lemma removes (p : Script) : Remainders p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨0,C c,0,by simp [tailMap]⟩
  | add p r h k =>
    obtain ⟨q,u,v,rfl⟩ := h; obtain ⟨s,t,w,rfl⟩ := k
    exact ⟨q+s,u+t,v+w,by rw [map_add,map_add]; ring⟩
  | mul_X p i h =>
    obtain ⟨q,u,v,rfl⟩ := h
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · refine ⟨X 0*q+tailMap v, -(tailS*v),u,?_⟩
      rw [map_neg,map_mul,chart_tail]; ring
    refine ⟨q*X i.succ,u*X i,v*X i,?_⟩
    rw [map_mul,map_mul,show tailMap (X i)=X i.succ by simp [tailMap]]; ring

lemma chart_divides {p : Script} (h : ∀ x : Space, sq x=0 → aeval x p=0) : chart ∣ p := by
  classical
  obtain ⟨q,u,v,rfl⟩ := removes p
  have hx (x : Fin 3 → ℂ) (t : ℂ) (ht : t^2= -aeval x tailS) : aeval x u+t*aeval x v=0 := by
    let b : Space := Fin.cons t x
    have hb : (fun i : Fin 3 ↦ b i.succ)=x := by simp [b,Axis]
    have hs : sq b=0 := by rw [←chart_at,chart_tail,map_add,map_pow,aeval_X, tail_at,hb, show b 0=t from rfl,ht,neg_add_cancel]
    have H := h b hs
    rwa [map_add, map_add,map_mul, map_mul,chart_at, hs, mul_zero, zero_add, aeval_X, tail_at,tail_at,hb, show b 0=t from rfl] at H
  have he (x : Fin 3 → ℝ) (hz : x 0 > 0) : let f i : ℂ := x i; aeval f u=0 ∧ aeval f v=0 := by
    intro f
    let w := ∑ i, (x i)^2
    have hw : 0 < w := Finset.sum_pos' (fun _ _ ↦ by positivity) ⟨0,Finset.mem_univ _,by positivity⟩
    have hb : aeval f tailS=(w:ℂ) := by simp [tailS,f,w]
    let t := I * ↑(Real.sqrt w)
    have ht : t≠0 := mul_ne_zero I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hw).ne')
    have hv : t^2= -aeval f tailS := by unfold t; rw [hb,mul_pow,I_sq,← ofReal_pow, Real.sq_sqrt hw.le]; ring
    have K := hx f t hv; have W := hx f (-t) (by simpa using hv)
    have hp : aeval f v=0 := by
      rw [neg_mul,add_neg_eq_zero] at W
      rw [W, ←two_mul,mul_eq_zero] at K
      exact (mul_eq_zero.mp (K.resolve_left (by norm_num))).resolve_left ht
    rw [hp,mul_zero,add_zero] at K; exact ⟨K,hp⟩
  let s := (fun i:ℕ ↦ (↑(i+1:ℕ):ℂ))
  have hu : Injective s := fun i j h ↦ by unfold s at h; norm_cast at h; omega
  have hW {x : Fin 3 → ℂ} (hw : x∈ Set.pi univ (fun _ ↦ range s)) : aeval x u=0 ∧ aeval x v=0 := by
    choose k hk using fun i ↦ hw i (mem_univ i)
    rw [show x=(fun i ↦ (↑((↑(k i+1:ℕ):ℝ)):ℂ)) by funext i; rw [← hk]; simp [s]]
    exact he (fun i ↦ (↑(k i+1:ℕ):ℝ)) (by positivity)
  have hU : u=0 := MvPolynomial.funext_set (fun _ ↦ Set.range s) (fun _ ↦ infinite_range_of_injective hu) (fun _ h ↦ ((hW h).1.trans (map_zero _).symm))
  have hV : v=0 := MvPolynomial.funext_set (fun _ ↦ Set.range s) (fun _ ↦ infinite_range_of_injective hu) (fun _ h ↦ ((hW h).2.trans (map_zero _).symm))
  refine ⟨q, ?_⟩; rw [hU,hV]; simp [mul_comm]

/-- rank-one matrix chart covering cone. including zero. -/

def spin (a b c d : ℂ) : Space := ![(a*c+b*d)/2, (b*d-a*c)/2*I, (a*d-b*c)/2, -(a*d+b*c)/2*I]

lemma fold0 (a b c d : ℂ) : sq (spin a b c d) = 0 := by
  simp only [sq,dot,Axis, Fin.sum_univ_four,spin]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  ring_nf; simp [I_sq]; ring_nf; simp

def plus (x : Space) := x 0 + x 1 * I
def minus (x : Space) := x 0 - x 1 * I
def right (x : Space) := x 2+x 3 * I
def left (x : Space) := -x 2+x 3 * I

lemma fold_plus (a b c d : ℂ) : plus (spin a b c d) = a*c := by simp [plus,spin]; ring_nf; simp; ring
lemma fold_minus (a b c d : ℂ) : minus (spin a b c d) = b*d := by simp [minus,spin]; ring_nf; simp; ring
lemma fold_right (a b c d : ℂ) : right (spin a b c d) = a*d := by simp [right,spin]; ring_nf; simp; ring
lemma fold_left (a b c d : ℂ) : left (spin a b c d) = b*c := by simp [left,spin]; ring_nf; simp; ring
lemma folded (x : Space) : plus x * minus x - right x * left x = sq x := by simp [plus,minus,right,left,sq,dot,Axis,Fin.sum_univ_four]; ring_nf; simp; ring
lemma fold_equal {x y : Space} (hp : plus x=plus y) (hm : minus x=minus y) (hr : right x=right y) (hl : left x=left y) : x=y := by
  have ht : ∀ a b c d : ℂ, a+b*I=c+d*I → a-b*I=c-d*I → a=c ∧ b=d := by
    intro a b c d h g; constructor
    · linear_combination (h+g)/2
    apply mul_right_cancel₀ I_ne_zero
    linear_combination (h-g)/2
  have h := ht _ _ _ _ hp hm
  unfold right at hr; unfold left at hl
  have w := ht _ _ _ _ hr (show x 2-x 3*I=y 2-y 3*I by linear_combination -hl)
  ext1 i; fin_cases i
  exacts [h.1,h.2,w.1,w.2]

lemma foldOnto {x : Space} (h : sq x=0) : ∃ a b c d, spin a b c d=x := by
  let p := plus x; let q := right x; let r := left x; let s := minus x
  have hx : p*s=q*r := sub_eq_zero.mp ((folded x).trans h)
  suffices hv : ∃ (a b c d : ℂ), a*c=p ∧ b*d=s ∧ a*d=q ∧ b*c=r by
    obtain ⟨a,b,c,d,h,f,g,k⟩ := hv; exact ⟨a,b,c,d,fold_equal (by rw [fold_plus]; exact h) (by rw [fold_minus]; exact f) (by rw [fold_right]; exact g) (by rw [fold_left]; exact k)⟩
  rcases eq_or_ne p 0 with hw|hn; swap
  · refine ⟨1,r/p,p,q,one_mul _, ?_,one_mul _,?_⟩
    · field_simp; linear_combination -hx
    field_simp
  rw [hw,zero_mul,eq_comm,mul_eq_zero] at hx
  rcases hx with hv|hr
  · exact ⟨0,1,r,s,by simp [hw,hv]⟩
  exact ⟨q,s,0,1,by simp [hw,hr]⟩

def propeller : Script →ₐ[ℂ] Script :=
  let k := X 0*X 2; let m := X 0*X 3; let n := X 1*X 2; let h := X 1*X 3
  aeval ![C 2⁻¹*(k+h), C (2⁻¹*I)*(h-k), C 2⁻¹*(m-n), C (-2⁻¹*I)*(m+n)]

lemma foldSub (p : Script) (b : Space) : aeval b (propeller p) = aeval (spin (b 0) (b 1) (b 2) (b 3)) p := by
  induction p using MvPolynomial.induction_on with
  | C => simp [propeller]
  | add p q hp hq => rw [map_add,map_add,map_add,hp,hq]
  | mul_X p i hp => rw [map_mul,map_mul,map_mul,hp]; unfold propeller; simp only [aeval_X]; congr 1; fin_cases i <;> simp [spin] <;> ring

def Obstructs (p : Script) := ∀ x : Space,sq x=0 → aeval x p=0
lemma coneChecks (p : Script) : Obstructs p ↔ propeller p=0 := by
  constructor
  · intro h; refine MvPolynomial.funext (fun x ↦ (Eq.trans (foldSub p x) (Eq.trans (h _ (fold0 ..)) (map_zero (MvPolynomial.eval x)).symm)))
  intro h x hx; obtain ⟨a,b,c,d,rfl⟩ := foldOnto hx
  have he := foldSub p ![a,b,c,d]; rw [h,map_zero] at he; exact he.symm
lemma cone_mul {p q : Script} : Obstructs (p*q) ↔ Obstructs p ∨ Obstructs q := by simp only [coneChecks,map_mul,mul_eq_zero]
lemma cone_ok {p q : Script} (hp : ¬ Obstructs p) (hq : ¬Obstructs q) : ¬ Obstructs (p*q) := fun h ↦ (cone_mul.mp h).elim hp hq
lemma pierce {p q : Script} (hp : ¬ Obstructs p) (h : ∀ x : Space, sq x=0 → aeval x p ≠ 0 → aeval x q=0) : Obstructs q := by
  apply Or.resolve_left (cone_mul.mp ?_) hp
  intro x hx; rw [map_mul]; by_cases he : aeval x p=0; · rw [he,zero_mul]
  rw [h x hx he,mul_zero]

def plot (x : Space) : Script := ∑ i:Axis, X i*C (x i)
lemma plot_at (x b : Space) : aeval b (plot x)=dot b x := by simp [plot,dot]
lemma plots {x : Space} (h : x ≠ 0) : ¬Obstructs (plot x) := by
  intro hv
  have hu (a b c d : ℂ) : dot (spin a b c d) x=0 := by rw [← plot_at]; exact hv _ (fold0 ..)
  have he : x=0 := by
    have i := hu 1 0 1 0; have j := hu 0 1 0 1; have k := hu 1 0 0 1; have l := hu 0 1 1 0
    simp [dot,spin,Axis, Fin.sum_univ_four] at i j k l
    ext1 a; change x a=0; fin_cases a
    · change x 0=0; linear_combination i+j
    · change x 1=0; apply mul_left_cancel₀ I_ne_zero
      linear_combination j-i
    · change x 2=0; linear_combination k-l
    change x 3=0; apply mul_left_cancel₀ I_ne_zero
    linear_combination -(k+l)
  exact h he
end YM.SchemeConversionRG11.Corona
