import YM.Pressure.Cost
/-!
# Travel of a flat physical field

 Even on torus, **cover-coordinate** displacement determines travel. Use signed fine
 links directly, no inversion regulator. Used here to test other would-be saddles of
 bare *conditional* step. Doesn't analyze the global law with torons removed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory Lattice Wilson
variable {f : Side} {K : Type} [Group K] {U : Links (Per f) K}

def Flat (U : Links (Per f) K) : Prop:= ∀ i:Face (Per f), faceValue U i=1

private def shoot (i : Axis) (U : Links (Per f) K) : Equiv.Perm (Site f × K) where
   toFun x:=(x.1+Lattice.step i,x.2*U (x.1,i))
   invFun x:=(x.1-Lattice.step i,x.2*(U (x.1-Lattice.step i,i))⁻¹)
   left_inv x:=by simp
   right_inv x:=by simp
private lemma Flat.turn (h : Flat U) (i j:Axis) (p:Site f) (he : i<j) :
   U (p,i) * U (p+Lattice.step i,j) = U (p,j)*U (p+Lattice.step j,i) := by
    have ht:= h (p,⟨(i,j),he⟩); rw [Pressure.corners] at ht; dsimp only at ht
    rw [← mul_inv_eq_one]; rw [← ht]; group
private lemma Flat.pivot (h : Flat U) (i j:Axis): Commute (shoot i U) (shoot j U) := by
   apply Equiv.ext ?_
   intro p; obtain ⟨p,x⟩:=p
   change (p+step j+step i,x*U (p,j)* U (p+step j,i))=(p+step i+step j,x*U (p,i)*U (p+step i,j));
   rw [add_right_comm p]; refine Prod.ext rfl ?_
   dsimp only; rw [mul_assoc x,mul_assoc]
   rcases lt_trichotomy i j with he|he|he; rw [h.turn i j p he]; rw [he]; rw [h.turn j i p he]

def pathLength : Walk→Cover
  | []=>0
  | d::t=> d.vec + pathLength t
lemma target (x : Site f) (w : Walk): stop x w = x+wrap f (pathLength w) := by
   induction w generalizing x with
   | nil=> rw [stop,pathLength,map_zero,add_zero]
   | cons d t ih=> rw [pathLength,stop, map_add,wrap_vec,ih,add_assoc]
lemma summit (x : Cover) (w : Walk): stop x w= x+pathLength w := by
   induction w generalizing x with
   | nil=> rw [stop,pathLength,add_zero]
   | cons d t ih=> rw [pathLength,stop,ih,add_assoc]

private def occupy (U : Links (Per f) K) (x : Cover) : Equiv.Perm (Site f × K) := shoot 0 U ^ x 0 * shoot 1 U ^ x 1 * shoot 2 U ^ x 2 * shoot 3 U ^ x 3
variable (h : Flat U)
include h
local notation "L"=>occupy U
private lemma pivots (i j : Axis) (x y : ℤ) : Commute (shoot i U^x) (shoot j U^y) := ((h.pivot i j).zpow_left x).zpow_right y
omit h [Group K] in
private lemma fold {a b c d:Equiv.Perm (Site f × K)} (h : Commute b c) : a*b*(c*d)=a*c*(b*d) := by rw [mul_assoc a b,← mul_assoc b c,h.eq,mul_assoc c b, ← mul_assoc]
private lemma occupy_add (x y : Cover) : L (x+y)=L x * L y:= by
   simp only [occupy,Pi.add_apply,zpow_add]
   rw [fold (pivots h 0 1 ..),fold (Commute.mul_left (pivots h 0 2 ..) (pivots h 1 2 ..)),fold ((Commute.mul_left (pivots h 0 3 ..) (pivots h 1 3 ..)).mul_left (pivots h 2 3 ..))]

-- sign uses inverse link. 
omit h in private lemma advance (x : Site f) (w : K) (d : Step) : L d.vec (x,w)=(x+d.vec,w*d.read U x):= by
   rcases d with ⟨i,v|v⟩
   · change L (Lattice.step i) (x,w)=(x+step i,w* U (x,i)); fin_cases i <;> simp [occupy,Lattice.step] <;> rfl
   change L (-Lattice.step i) (x,w)=(x+-step i,w* (U (x-step i,i))⁻¹); rw [← sub_eq_add_neg]; fin_cases i <;> simp [occupy,Lattice.step] <;> rfl

private lemma atStep (x : Site f) (v : K) (t : Walk) :
    L (pathLength t) (x,v)=(stop x t,v*travel U x t) := by
   induction t generalizing x v with
   | nil=>simp [travel,stop,pathLength,occupy]
   | cons d t ih=> rw [pathLength,stop,travel,add_comm (d.vec : Cover),occupy_add h, Equiv.Perm.mul_apply,advance,ih,mul_assoc]
lemma journey (a b : Walk) (x : Site f) (he : pathLength a=pathLength b) : travel U x a = travel U x b := by
   have ht:= congrArg Prod.snd ((atStep h x 1 a).symm.trans ((congrArg (fun p:Cover=>L p (x,1)) he).trans (atStep h x 1 b)))
   simpa only [one_mul] using ht
end YM.Comparison.RG02.Bare
