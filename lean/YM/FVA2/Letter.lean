import YM.FVA2.Acyclic
import YM.MS.Bare.Focus

/-!
# Flat BV complex with *based* gauge parameters

Signs agreed in derivative order before passing between Fourier and position
polarizations. `X` represents real (log) link variables, `Y` independent
site variables, no antifield sources on the observables at this step.
`grad` is the linearized gauge action, `hes` the cost Hessian (exponent -cost).
-/
set_option autoImplicit false

noncomputable section

namespace YM.FVA2
open Function Set Finset Matrix MS MS.Koszul MS.Bare MS.Book MS.Cylinder

namespace OddMatrix

lemma as_derivation {A : Type} [Fintype A] (p : Sector A) (m : Matrix A A ℂ)
    (h : Swaps p m) (F : Raw A ℂ) (hF : Symm p F) :
    (lift p m h).Q F = ∑ x:A, product p (atLetter x) ((lift p m h).hook x F) := by
  classical
  let X := lift p m h
  funext l
  induction l generalizing F with
  | nil =>
    rw [Shift.nil,Finset.sum_apply]; symm
    exact Finset.sum_eq_zero fun i _ => by simp [atLetter]
  | cons i l IH =>
    have he : ∑ x:A, product p (D i (atLetter x)) (X.hook x F)= X.hook i F := by
      rw [Finset.sum_eq_single_of_mem i (mem_univ _), hear, coin_product, one_smul]
      intro x _ hx; rw [unheard _ (Ne.symm hx),map_zero]; rfl
    have hs (x : A) : product p (MS.Koszul.sign p (p i) (atLetter x)) (D i (X.hook x F))=
        (cross true (p i):ℂ) • product p (atLetter x) (X.hook x (D i F)) := by
      rw [(speaks_p x).signs, X.hook_deriv x F i hF,map_smul,map_smul,
        LinearMap.smul_apply]
      rw [smul_smul,cross_left,cross_comm (p x) (p i),mul_assoc,cross_cross,mul_one]
    change X.Q F _ = (∑ x:A, product p (atLetter x) (X.hook x F)) _
    rw [D_eval _ (X.Q F),D_eval _ (∑ x:A, product p (atLetter x) (X.hook x F))]
    simp_rw [map_sum, X.deriving', D_product, hs, Finset.sum_add_distrib, he,
      ← Finset.smul_sum, Pi.add_apply, Pi.smul_apply]
    change X.hook i F l + _ = _
    exact congr_arg (fun x => X.hook i F l + (cross true (p i):ℂ) • x) (IH _ (hF.drop i))
end OddMatrix

/-- Oriented field/antifield/ghost alphabet. -/
inductive Letter (X Y : Type)
| a : X → Letter X Y
| k : X → Letter X Y
| c : Y → Letter X Y
| b : Y → Letter X Y
  deriving DecidableEq, Fintype

namespace Letter
variable {X Y : Type}

def p : Sector (Letter X Y)
| a _ | b _ => false
| k _ | c _ => true

private def outerEquiv : ((X ⊕ X) ⊕ (Y ⊕ Y)) ≃ Letter X Y where
  toFun := Sum.elim (Sum.elim a k) (Sum.elim c b)
  invFun
    | a x => .inl (.inl x)
    | k x => .inl (.inr x)
    | c y => .inr (.inl y)
    | b y => .inr (.inr y)
  left_inv x := by rcases x with (u|u)|(v|v) <;> rfl
  right_inv x := by cases x <;> rfl

lemma sum_all [Fintype X] [Fintype Y] {T : Type*} [AddCommMonoid T] (f : Letter X Y → T) :
    ∑ i : Letter X Y, f i = ((∑ i, f (a i)) + ∑ i, f (k i)) +
      ((∑ i, f (c i)) + ∑ i, f (b i)) := by
  rw [← Equiv.sum_comp outerEquiv f]
  simp_rw [Fintype.sum_sum_type]
  rfl

def bond (X Y : Type) : Bonded (@p X Y) (X ⊕ Y) := {
  plain := ⟨Sum.elim a c, by
    rintro (x|x) (y|y) h <;> simp_all⟩
  dual := ⟨Sum.elim k b, by
    rintro (x|x) (y|y) h <;> simp_all⟩
  diff := by rintro (x|x) (y|y) <;> (
             simp only [Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr]; intro hh; cases hh)
  wave i := by cases i <;> rfl }

def focus (X Y : Type) : Focus (bond X Y) X Y where
  call := Equiv.refl _
  act _ := rfl
  gauge _ := rfl

section Shift
open OddMatrix
variable [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]
variable (hes : Matrix X X ℂ) (grad : Matrix X Y ℂ)
  (cov : Matrix X X ℂ) (l : Matrix Y X ℂ)

def q : Matrix (Letter X Y) (Letter X Y) ℂ
| c i, a j => grad j i
| a i, k j => -hes j i
| k i, b j => grad i j
| _, _ => 0

def lower : Matrix (Letter X Y) (Letter X Y) ℂ
| a i, c j => l j i
| k i, a j => -cov j i
| b i, k j => l i j
| _, _ => 0

omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
lemma q_odd : Swaps p (q hes grad) := by
  rintro (_|_|_|_) (_|_|_|_) h <;> first | rfl | exact (h rfl).elim

omit [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y] in
lemma lower_odd : Swaps p (lower cov l) := by
  rintro (_|_|_|_) (_|_|_|_) h <;> first | rfl | exact (h rfl).elim

abbrev Q := OddMatrix.lift p (q hes grad) (q_odd hes grad)
abbrev Δ := (bond X Y).BV (R:=ℂ)

variable {hes grad cov l}

omit [DecidableEq X] [DecidableEq Y] in
lemma q_squared (hh : hesᵀ=hes) (hg : hes*grad=0) : q hes grad * q hes grad = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply, sum_all]
  rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> simp [q]
  · simp_rw [show ∀ x,hes x i = hes i x from fun (x:X) => congr_fun (congr_fun hh i) x]
    exact congr_fun (congr_fun hg i) j
  simp_rw [mul_comm (grad _ _)]; exact congr_fun (congr_fun hg j) i

lemma q_contraction (hh : hesᵀ=hes) (hs : covᵀ=cov) (hm : l*grad=1)
    (hc : cov*hes=1-grad*l) : lower cov l * q hes grad + q hes grad * lower cov l = 1 := by
  have ht : hes*cov = 1-lᵀ*gradᵀ := by
    nth_rw 1 [← hh, ← hs]
    rw [← Matrix.transpose_mul,hc]
    simp
  ext i j
  simp_rw [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, sum_all]
  rcases i with i|i|i|i <;> rcases j with j|j|j|j <;> simp [q,lower]
  · have he := congr_fun (congr_fun hc j) i
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply] at he
    simp_rw [mul_comm (l _ _), mul_comm (hes _ _)]; rw [he]; simp only [eq_comm (a:=j) (b:=i)]; abel
  · have he:=congr_fun (congr_fun ht j) i
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, transpose_apply] at he
    simp_rw [mul_comm (cov _ _),mul_comm (grad _ _)]; rw [he]; simp only [eq_comm (a:=j) (b:=i)]; abel
  · have he:= congr_fun (congr_fun hm j) i
    simp_rw [mul_comm (grad _ _)]; simp only [eq_comm (a:=i) (b:=j)]; exact he.trans Matrix.one_apply
  exact (congr_fun (congr_fun hm i) j).trans Matrix.one_apply

variable (F : Raw (Letter X Y) ℂ)

omit [DecidableEq X] [DecidableEq Y] in
lemma delta (F : Raw (Letter X Y) ℂ) : Δ F =
    (∑ x : X, D (a x) (D (k x) F)) - ∑ y : Y, D (c y) (D (b y) F) := by
  simp_rw [Δ, Bonded.BV, loop, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [bond, diffPair_apply, LinearMap.smul_apply, Bonded.fee,
    Function.Embedding.coeFn_mk, Sum.elim_inl, Sum.elim_inr, p, cross_true,
    cross_false, neg_smul, one_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

omit [DecidableEq X] [DecidableEq Y] in
lemma symm_delta (hF : Symm p F) : Symm p (Δ F) := loop_symm hF

omit [DecidableEq X] [DecidableEq Y] in
lemma limit_delta (n : ℤ) (hF : Limit F n) : Limit (Δ F) (n-2) := by
  rw [delta, show n-2 = n-1-1 from by omega]
  exact (Limit.sum _ (f:=fun x:X=>D (a x) (D (k x) F)) (fun x _=>(hF.tip _).tip _)).sub
    (Limit.sum _ fun y _ => (hF.tip (b y)).tip _)

omit [DecidableEq X] [DecidableEq Y] in
lemma square_delta (hF : Symm p F) : Δ (Δ F)=0 := by
  have H : Δ (Δ F) = (-1:ℂ) • Δ (Δ F) :=
    loop_loop (bond X Y).costs (bond X Y).costs hF
  ext v
  have Hv := congr_fun H v
  simp only [Pi.smul_apply, smul_eq_mul, neg_mul, one_mul] at Hv
  change Δ (Δ F) v=0
  apply mul_left_cancel₀ (two_ne_zero : (2:ℂ)≠0)
  rw [two_mul, mul_zero, show Δ (Δ F) v + _ = _ from congr_arg (fun x:ℂ=> x + Δ (Δ F) v) Hv,neg_add_cancel]

omit [DecidableEq X] [DecidableEq Y] in
lemma commute_deltas (hF : Symm p F) (hh : hesᵀ=hes) :
    Δ ((Q hes grad).Q F) = -(Q hes grad).Q (Δ F) := by
  let T := Q hes grad
  have ha (x:X) : D (a x) (D (k x) (T.Q F)) =
      (∑ y:Y, grad x y • D (a x) (D (b y) F)) +
      (∑ i:X, hes i x • D (k i) (D (k x) F)) -
        T.Q (D (a x) (D (k x) F)) := by
    rw [T.deriving',map_add,map_smul,T.deriving']
    change D _ ((OddMatrix.lift p _ (q_odd hes grad)).hook _ F)+
      (cross true true:ℂ) • ((OddMatrix.lift p _ (q_odd hes grad)).hook _ _ + (cross true false:ℂ) • _) = _
    rw [hook_apply,hook_apply,sum_all,sum_all]
    simp [q, sub_eq_add_neg]
    abel
  have hb (i:Y) : D (c i) (D (b i) (T.Q F)) =
      (∑ x:X, grad x i • D (a x) (D (b i) F)) -
        T.Q (D (c i) (D (b i) F)) := by
    rw [T.deriving',map_add,map_smul,T.deriving']
    change D _ ((OddMatrix.lift p _ (q_odd hes grad)).hook _ F)+
      (cross true false:ℂ) • ((OddMatrix.lift p _ (q_odd hes grad)).hook _ _ + (cross true true:ℂ) • _) = _
    rw [hook_apply,hook_apply,sum_all,sum_all]
    simp [q, sub_eq_add_neg]
  have hc : (∑ x:X,∑ i:X, hes i x • D (k i) (D (k x) F)) = 0 := by
    let U := ∑ x:X,∑ i:X, hes i x • D (k i) (D (k x) F)
    have ht : U = -U := by
      unfold U; nth_rw 1 [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro i _
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hF.commute (k i) (k j), show hes i j = hes j i from congr_fun (congr_fun hh j) i]
      simp [p]
    ext v; change U v=0; apply mul_left_cancel₀ (two_ne_zero : (2:ℂ)≠0); rw [two_mul,mul_zero]; exact (congr_arg (fun x:ℂ=>x+U v) (congr_fun ht v)).trans (neg_add_cancel (U v))
  change Δ (T.Q F)= -T.Q (Δ F)
  rw [delta,delta]
  simp_rw [ha,hb,map_sub,map_sum,sum_sub_distrib,sum_add_distrib,hc]
  rw [Finset.sum_comm (f:=fun x y=>grad x y • D (a x) (D (b y) F))]
  abel

omit [DecidableEq X] [DecidableEq Y] in
lemma square (hv : hesᵀ=hes) (hm : hes*grad=0) (hF : Symm p F) :
    (Δ (X:=X) (Y:=Y) + (Q hes grad).Q) ((Δ (X:=X) (Y:=Y) + (Q hes grad).Q) F) = 0 := by
  simp only [LinearMap.add_apply, map_add, square_delta _ hF,
    commute_deltas F hF hv, show (Q hes grad).Q ((Q hes grad).Q F)=0 from
      Q_sq_zero _ F (q_squared hv hm)]
  abel

end Shift
end Letter
end YM.FVA2
