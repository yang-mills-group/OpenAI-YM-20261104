import YM.XSpace.Central

/-!
# Scalar and color coordinate tools on the letter jets

Projector onto exact difference samples; bound the cost per degree on
any shell. Grade lowering via playing derivatives (order matters in the
proof but the tensors are symmetric).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Litter
open Lattice Maxwell Maxwell.Free Tensor Filter Function Sail Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{n:ℕ}

def stack (v:Fin n→Axis)(p:F) : piece n F := (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) p).compContinuousLinearMap (fun i=> EuclideanSpace.proj (v i))
lemma stack_on (v:Fin n→Axis)(p:F)(A:Fin n→E4): stack v p A=(∏ i: Fin n,A i (v i)) • p:=rfl
lemma stack_test (v w:Fin n→Axis)(p:F): stack v p (basis ∘ w)=if w=v then p else 0:=by
  rw [stack_on]; split_ifs with h
  · subst v; simp
  obtain ⟨i,hi⟩:= Function.ne_iff.mp h; rw [Finset.prod_eq_zero (Finset.mem_univ i),zero_smul]; simp [Ne.symm hi]
def sticker (v:(Fin n→Axis)→F): piece n F:= ∑ t:Fin n→Axis, stack t (v t)
lemma sticker_on (v:(Fin n→Axis)→F)(t:Fin n→Axis):sticker v (basis ∘ t)=v t:=by simp [sticker,stack_test]
lemma piece_ext {A B:piece n F}(h:∀ t:Fin n→Axis,A (basis∘t)=B (basis∘t)): A=B:=by
  apply ContinuousMultilinearMap.ext; intro v
  let f (i:Fin n)(a:Axis):= v i a • basis a
  have he (C:piece n F): C v=∑ t:Fin n→Axis,(∏ i:Fin n,v i (t i)) • C (basis ∘ t):=by
    conv_lhs=> arg 2; rw [show v=fun i:Fin n=> ∑ a:Axis,f i a from funext fun i=>(dirs _).symm];
    exact (C.map_sum f).trans (Finset.sum_congr rfl fun i _=> (C.map_smul_univ (fun j=>v j (i j)) (basis∘i)))
  rw [he, he]; simp_rw [h]
def stamps (F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F](n:ℕ): Submodule ℝ (piece n F) where
  carrier:= {A|Sym A}
  zero_mem':=fun _ _=>rfl
  add_mem':=by rintro a b (ha:Sym a) (hb:Sym b) v s; simp [ha _ s,hb _ s]
  smul_mem':=by rintro r x (h:Sym x) v s; simp [h _ s]
abbrev Stamp (n:ℕ)(F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F]:= ↥(stamps F n)
def dip (i: Axis): Stamp (n+1) F →ₗ[ℝ] Stamp n F where
  toFun A := ⟨((n+1:ℕ):ℝ) • A.val.curryLeft (basis i), fun v s=> congr_arg (((n+1:ℕ):ℝ) • ·) (freeze_sym A.val A.property _ v s)⟩
  map_add' A B := by apply Subtype.ext; ext1 v; change ((n+1:ℕ):ℝ) • (A.val _ + B.val _) = _; rw [smul_add]; rfl
  map_smul' a b:= Subtype.ext (ContinuousMultilinearMap.ext fun _=> smul_comm (((n+1:ℕ):ℝ)) a (_:F))

def feed (v:E4): Stamp n F→ₗ[ℝ] (Cover→F):= LinearMap.pi fun x=> (board (rcast x+v)) ∘ₗ (stamps F n).subtype
lemma rcast_step_add (x:Cover)(i:Axis):rcast (x+step i)= rcast x+basis i:=by ext l; simp [rcast,step,basis]; split_ifs <;> simp_all
lemma feed_one (x:Cover)(i:Axis)(v:E4)(A:Stamp (n+1) F): Δf i (feed v A) x= feed (v+half i) (dip i A) x:=by
  change board (rcast (x+step i) + v) A.val - board (rcast x+v) A.val= _; rw [rcast_step_add,← twice, show rcast x+(half i+half i)+v=rcast x+(v+half i)+half i by abel, show rcast x+v=rcast x+(v+half i)-half i by abel]; exact plays A.val A.property i _
lemma feed_const (v:E4)(i:Axis)(A:Stamp 0 F): Δf i (feed v A)=0:=by funext x; change board _ A.val-board _ A.val=(0:F); rw [steady,steady, sub_self]

def teeth (i:Axis): (Cover→F) →ₗ[ℝ](Cover→F) where
  toFun:=Δf i
  map_add' u v:= funext fun _=> add_sub_add_comm (u _) (v _) _ _
  map_smul' a u:= funext fun _=> (smul_sub a (u _) (u _)).symm
def peak : List Axis → Module.End ℝ (Cover→F)
| []=> LinearMap.id
| i::s => teeth i ∘ₗ peak s
lemma peaked (A:List Axis)(v:Cover→F): peak A v= crack A v:=by induction A with | nil=>rfl | cons i A ih=> exact congr_arg (Δf i) ih
lemma chosen (i j:Axis)(v:Cover→F): Δf i (Δf j v)=Δf j (Δf i v):=by funext x; unfold Δf; simp only [add_right_comm x]; abel
lemma cracks_perm {A B:List Axis} (h:A.Perm B)(v:Cover→F):crack A v=crack B v:=by induction h with
  | nil=> rfl
  | cons a _ ih=> exact congr_arg (Δf a) ih
  | swap a b l=> exact chosen ..
  | trans _ _ ih1 ih2=> exact ih1.trans ih2
lemma snack (i:Axis)(A: List Axis)(v:Cover→F): crack (i::A) v=crack A (Δf i v):=by induction A with
  | nil=> rfl
  | cons j A ih=> change Δf i (Δf j (crack A v))=Δf j _; rw [chosen, show Δf i (crack A v)= _ from ih]

def felt (v:E4)(A:Stamp n F)(l:List Axis): Cover→F:= crack l (feed v A)
lemma sent (v:E4)(A:Stamp n F)(x:Cover)(t: Fin n→Axis) : felt v A (List.ofFn t) x=((n.factorial:ℝ)) • A.val (basis ∘ t) :=by
  induction n generalizing v with
  | zero=>rw [List.ofFn_zero]; simp; change board _ A.val=_; exact (steady A.val (rcast x+v)).trans (congr_arg A.val (Subsingleton.elim ..))
  | succ n ih=>
    let i:= t 0; let s:=Fin.tail t; unfold felt; rw [List.ofFn_succ,snack, funext fun x=> feed_one x i v A]; change felt (v+half i) (dip i A) (List.ofFn s) x=_; rw [ih _ (dip i A) s]
    change (_:ℝ) • ((n+1:ℕ):ℝ) • A.val (Fin.cons _ _) = _; rw [show (basis ∘ t)= Fin.cons (basis i) (basis ∘ s) from funext fun j=>by cases j using Fin.cases <;> rfl,smul_smul,Nat.factorial_succ,Nat.cast_mul,mul_comm]
lemma late (v:E4)(A:Stamp n F){l:List Axis}(h:n<l.length): felt v A l=0:=by
  induction n generalizing l v with
  | zero=> cases l with
           | nil=> simp at h
           | cons i l=> unfold felt; rw [snack,feed_const,← peaked,map_zero]
  | succ n ih=> cases l with
                | nil=> simp at h
                | cons i l=> unfold felt; rw [snack,funext fun x=>feed_one x i v A]; apply ih; simp at h; exact h
lemma once_hard (v:E4): Injective (feed (n:=n) (F:=F) v):= by
  intro x y h; apply Subtype.ext; apply piece_ext; intro t; apply smul_right_injective F (by positivity : (n.factorial:ℝ)≠0); dsimp only; rw [← sent v x 0, ← sent v y 0]; rw [felt,felt,h]

private lemma seats (v:E4) : ∃ C:ℝ,0<C∧ ∀ x:Cover, 1+‖rcast x+v‖ ≤ C*(1+reach x):=by
  refine ⟨3+‖v‖,by positivity,fun x=>?_⟩; nlinarith [(west x).2,norm_add_le (rcast x) v,mul_nonneg (norm_nonneg v) (Nat.cast_nonneg (reach x) (α:=ℝ))]
lemma dip_price (n:ℕ)(i:Axis): ∃ C:ℝ,0<C∧ ∀ A:Stamp (n+1) F, ‖dip i A‖ ≤ C*‖A‖:=by
  refine ⟨(n:ℝ)+1,by positivity,fun A=>?_⟩; change ‖((n+1:ℕ):ℝ) • A.val.curryLeft (basis i)‖ ≤ _; rw [norm_smul]; push_cast; rw [Real.norm_of_nonneg (by positivity)]; gcongr; simpa using A.val.curryLeft.le_opNorm (basis i)
lemma pay (l:List Axis)(v:E4)(n:ℕ) : ∃ C:ℝ,0<C∧∀ (x:Cover)(A:Stamp n F), ‖felt v A l x‖ ≤ C*‖A‖*(1+reach x)^(n-l.length):=by
  induction l generalizing v n with
  | nil=> obtain ⟨C,hC,H⟩:= off_meter (F:=F) n; obtain ⟨D,hD,K⟩:= seats v; refine ⟨C*D^n,by positivity, fun x A=> le_trans (H A.val (rcast x+v)) ?_⟩; simp only [List.length_nil,Nat.sub_zero]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (K x) n) (by positivity : 0≤C*‖A.val‖)) (le_of_eq ?_); change _=C*D^n*‖A.val‖*_; rw [mul_pow]; ring
  | cons i l ih=>
    cases n with
    | zero=> refine ⟨1,by norm_num, fun x A=> ?_⟩; simp [late v A (show 0<(i::l).length by simp)]
    | succ n=>
      obtain ⟨C,hC,H⟩:= ih (v+half i) n; obtain ⟨D,hD,K⟩:=dip_price (F:=F) n i
      refine ⟨C*D,by positivity, fun x A=>?_⟩; rw [felt,snack,funext fun x=> feed_one x i v A]; apply le_trans (H x (dip i A)); rw [List.length_cons, Nat.add_sub_add_right, mul_assoc C D]; gcongr _ * ?_ * _; apply K
end YM.XSpace.Litter
