import YM.FVAAlt2.FormExp
import YM.FVAAlt2.Covariance

/-! Fermion Wick evaluation, step one: algebraic identities in the
actual even vertex ring. Names order: `psi` is antighost and `theta` ghost.
This is to get a determinant with BOSONIC entries, not after setting A=0. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Native MS.Plane MS.Book MS.Cylinder MS.Puff MS.Puff.Actors
open MS.Swirl MS.Puff.Mom MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal
open Function Finset
open scoped PowerSeries
set_option linter.unusedSectionVars false
namespace Glue
variable {ι κ B:Type} [Fintype ι][Fintype κ]
local notation "J" => Alpha ι κ
local infix:70 " ⋆ " => product isOdd
local notation "R" => Raw (Alpha ι κ) ℂ
abbrev psi (ι:Type)(i:κ): Raw (Alpha ι κ) ℂ:= atLetter (antigh i)
abbrev theta (ι:Type)(i:κ): Raw (Alpha ι κ) ℂ:= atLetter (gh i)

lemma poG (k:κ):Pure isOdd true (theta ι k):= speaks_p (gh k) (p:=isOdd (ι:=ι))
lemma poP (k:κ):Pure isOdd true (psi ι k):= speaks_p (antigh k) (p:=isOdd (ι:=ι))

/-- Matrix of even products of undifferentiated ghost letters. Row antighost,
column ghost. Sign tie accounted (theta then psi equals -psi then theta). -/
def pairG (ι:Type)[Fintype ι](i j:κ): Com (isOdd (ι:=ι) (κ:=κ)) :=by
  classical
  let A:=psi ι i; let C:=theta ι j
  refine ⟨C ⋆ A,Com.mem ((show Pure isOdd true C from poG (ι:=ι) j).prod (show Pure isOdd true A from poP (ι:=ι) i)) ?_⟩; exact fee_pair ⟨speaks_s _,minH (letterN _)⟩ ⟨speaks_s _,minH (letterN _)⟩

local notation "E" => Com (isOdd (ι:=ι) (κ:=κ))
local notation "p" => isOdd (ι:=ι) (κ:=κ)

lemma spelled (i j:κ): (pairG ι i j).val=theta ι j ⋆ psi ι i:= rfl
lemma clm {f g:R}(h:Pure p true f)(hp:Pure p true g) : f ⋆ g= -(g ⋆ f) := by simpa using h.times_comm hp
lemma anti (i j:κ): (pairG ι i j).val= -(psi ι i ⋆ theta ι j):= clm (poG j) (poP i)
lemma nil_odd {f:R}(h:Pure p true f): f ⋆ f=0:= by
  have he:=clm h h; have hx:(2:ℂ) • (f ⋆ f)=0:= by rw [two_smul]; nth_rw 1 [he]; abel
  exact (smul_eq_zero.mp hx).resolve_left (by norm_num)
lemma same_bar (i j k:κ): pairG ι i j * pairG ι i k=0:= by
  let f:=pairG ι i k
  apply Subtype.ext
  change (theta ι j ⋆ psi ι i) ⋆ f.val=0
  rw [times_assoc,(f.even.central _).symm, spelled i k, times_assoc, nil_odd (poP (ι:=ι) i), map_zero,map_zero]
lemma same_ghost (i j k:κ): pairG ι j i * pairG ι k i=0:= by rw [mul_comm]; apply Subtype.ext; rw [Com.mul_val,anti k i]; let f:=pairG ι j i; change product p (-(psi ι k ⋆ theta ι i)) f.val=_; rw [map_neg,LinearMap.neg_apply, times_assoc, spelled, ← times_assoc (theta ι i),nil_odd (poG (ι:=ι) i), map_zero,LinearMap.zero_apply,map_zero,neg_zero];rfl
lemma swap_ghost (i j k l:κ) : pairG ι i j *pairG ι k l = -(pairG ι i l *pairG ι k j):=by
  have hg (j k:κ): theta ι j ⋆ (pairG ι k l).val= -(theta ι l ⋆ (pairG ι k j).val):= by rw [spelled, spelled, ← times_assoc, clm (poG (ι:=ι) j) (poG (ι:=ι) l),map_neg,LinearMap.neg_apply,times_assoc]; -- binder i?
  apply Subtype.ext; rw [Submodule.coe_neg,Com.mul_val, Com.mul_val,anti i j,anti i l,map_neg,LinearMap.neg_apply,map_neg,LinearMap.neg_apply,times_assoc,times_assoc,hg j k,map_neg]

/-- `Silent` in antighost i. Derivative is the actual left derivative. -/
def Stops (i:κ) (F:Com (isOdd (ι:=ι) (κ:=κ))): Prop := D (antigh i) F.val=0
lemma stop_zero(i:κ):Stops i (0:E) := map_zero _
lemma stop_add{F Q:E}{i:κ}(h:Stops i F)(he:Stops i Q): Stops i (F+Q):=by unfold Stops; rw [Submodule.coe_add,map_add,show D _ _=0 from h,show D _ _=0 from he,zero_add]
lemma stop_smul{F:E}{i:κ}(h:Stops i F)(z:ℂ): Stops i (z • F):=by unfold Stops; rw [Submodule.coe_smul,map_smul,show D _ _=0 from h,smul_zero]
lemma stop_mul {F Q:E}{i:κ}(h:Stops i F)(he:Stops i Q): Stops i (F*Q):=by unfold Stops; rw [Com.mul_val,D_product,show D _ _=0 from h,show D _ _=0 from he,map_zero, LinearMap.zero_apply,map_zero,add_zero]
lemma stop_one(i:κ):Stops i (1:E) := rfl
lemma stop_sum (s:Finset B){f:B→E}(i:κ)(hp:∀ j∈s,Stops i (f j)): Stops i (∑ j∈s,f j):= by
  classical
  induction s using Finset.induction with
  | empty=> simp only [Finset.sum_empty]; exact stop_zero ..
  | insert x s h ih=> rw [Finset.sum_insert h]; exact stop_add (hp _ (mem_insert_self ..)) (ih (fun i hi=> hp i (mem_insert_of_mem hi)))
lemma stop_other {i j:κ}(k:κ)(h:i≠j):Stops i (pairG ι j k):=by
  unfold Stops; rw [spelled, D_product,unheard (gh k) (j:=antigh i) ?_,unheard (antigh j) ?_,map_zero,map_zero,LinearMap.zero_apply,add_zero]
  all_goals simp [antigh,gh,h]
end Glue
end YM.FVAAlt2
