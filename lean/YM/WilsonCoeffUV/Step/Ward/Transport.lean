import YM.WilsonCoeffUV.Step.Ward.Area

/-! Move the determinant to native single-slot coordinates, and the
analytic substitution into scaled z/w coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Function Matrix PowerSeries Filter Set
open scoped BigOperators Topology ContDiff
variable {X Y Z:Type*}[Fintype X][Fintype Y][Fintype Z][DecidableEq X][DecidableEq Y][DecidableEq Z]

-- product calculus
lemma leftGreen : Green (leftArm (U:=X) (V:=Y)) := by rw [show leftArm = fun v=>leftFlag X Y*ᵥ v from funext fun p=> (left_hit p).symm]; exact board _
lemma rightGreen : Green (rightArm (U:=X) (V:=Y)) := by rw [show rightArm = fun v=>rightFlag X Y*ᵥ v from funext fun p=> (right_hit p).symm]; exact board _
omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma leftZero : leftArm (0:Lawn (X⊕Y))=0 := rfl
omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
lemma rightZero : rightArm (0:Lawn (X⊕Y))=0 := rfl
omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
lemma sumGreen {A:Lawn X→Lawn Y}{B:Lawn X→Lawn Z}(h:Green A)(w:Green B): Green fun v=> Sum.elim (A v) (B v):= by
  apply contDiffAt_pi.mpr; intro i; cases i with
  | inl y=> exact (contDiffAt_apply ℝ ℝ y _).comp 0 h
  | inr z=> exact (contDiffAt_apply ℝ ℝ z _).comp 0 w
omit [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
lemma sumZero {A:Lawn X→Lawn Y}{B:Lawn X→Lawn Z}(h:A 0=0)(w:B 0=0): (Sum.elim (A 0) (B 0):Lawn (Y⊕Z))=0:= by funext s; cases s <;> simp [h,w]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
lemma spool_chain (A:Lawn X→ Lawn Y)(B:Lawn Y→Lawn Z)(ha:A 0=0)(hb:B 0=0)(h:Green A)(w:Green B) : (train (spool A)).comp (train (spool B)) = train (spool (B ∘ A)) := by
  have he j: train (spool A) (spool B j) = spool (B ∘ A) j := by
    have H : (B ∘ A) 0=0 := by rw [Function.comp_apply,ha,hb]
    apply mul_left_cancel₀ (a:=PowerSeries.X) X_ne_zero
    conv_lhs => arg 1; rw [← train_X (spool A)]
    rw [←map_mul, spool_raised _ hb,spool_raised _ H,traveling A h ha (fun u=>B u j) ((contDiffAt_apply ℝ ℝ j _).comp 0 w)]; rfl
  rw [through]; simp_rw [he]

omit [DecidableEq Z] in
lemma roll_shawl (A:Lawn (X⊕Y) → Lawn X)(B:Lawn Y→Lawn Z)(h:A 0=0)(w:Green B)(b:B 0=0):
    reroll (spool B) (spool A) = train (spool fun p=> Sum.elim (A p) (B (rightArm p))) := by
  let V:= fun p=> Sum.elim (A p) (B (rightArm p))
  have hz : (B ∘ rightArm (U:=X)) 0=0 := by rw [Function.comp_apply,rightZero,b]
  have hv: V 0=0:= sumZero h hz
  unfold reroll; congr 1; funext j; cases j with
  | inl v=> rfl
  | inr v=>
    change holdUp X (spool B v)= spool (B ∘ rightArm) v
    have H : holdUp X (Y:=Y)= train (spool rightArm) := by rw [←hold_loom,←spool_loom, show (fun v=>rightFlag X Y*ᵥ v)=rightArm from funext right_hit]
    rw [H];
    exact (by simpa only [RingHom.comp_apply,train_path] using DFunLike.congr_fun (spool_chain (rightArm (U:=X)) B rightZero b rightGreen w) (path v))

section determinant
-- column det identities
variable (F:Lawn (X⊕Y)→Lawn X)
def edgeM (u:Lawn (X⊕Y)) : Matrix X X ℝ:= of fun i j=> rub (fun p=> F p i) (Sum.inl j) u

omit [DecidableEq X] [DecidableEq Y] in
lemma edge_green (h:Green F)(i j) : Green fun v=>edgeM F v i j:= rubbed ((contDiffAt_apply ℝ ℝ i _).comp 0 h) _
-- compute determinant of arbitrary matrix of Greens via Levi
omit [DecidableEq X] in
lemma solar_prod {I:Type*}(s:Finset I)(f:I→ Lawn X→ℝ)(h:∀ i∈s,Green (f i)): jet (∏ i∈s,f i)=∏ i∈s,jet (f i):= by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.prod_empty]; exact (jet_const 1).trans (by rw [map_one])
  | @insert i s hi ih=>
    have he (j) (hj:j∈s):= h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, jet_mul (h i (Finset.mem_insert_self ..)) (show Green (∏ i∈s,f i) from ?g), ih he]
    case g=> rw [show (∏ i∈s,f i)=fun x=>∏ i∈s,f i x from funext fun i=>Finset.prod_apply ..]; exact contDiffAt_prod he
omit [DecidableEq Y] in
lemma solar_det {h:Lawn Y→Matrix X X ℝ}(H:∀ i j,Green fun x=>h x i j) : jet (fun x=>(h x).det) = (Matrix.of (fun i j=>jet fun x=> h x i j)).det := by
  have hC (s:Equiv.Perm X) : Green (fun x=>∏ i, h x (s i) i):= contDiffAt_prod (fun i _=>H ..)
  simp_rw [Matrix.det_apply'];
  let f (s:Equiv.Perm X) := (fun _:Lawn Y=> (↑(↑(Equiv.Perm.sign s):ℤ):ℝ))*fun x=>∏ i,h x (s i) i
  change jet (fun x=>∑ s, f s x)=_
  rw [show (fun x=>∑ s,f s x)= ∑ s,f s from funext fun x=> (Finset.sum_apply ..).symm,jet_sum _ f (fun s _=> ContDiffAt.mul contDiffAt_const (hC s))];
  apply Finset.sum_congr rfl; intro i _; unfold f
  rw [jet_mul (g:=fun x=> ∏ j,h x (i j) j) contDiffAt_const (hC i),jet_const,map_intCast];
  rw [show (fun x=>∏ j,h x (i j) j)= ∏ j,fun x=>h x (i j) j from funext fun x=> by rw [Finset.prod_apply],solar_prod _ _ (fun _ _=> H ..)]; rfl
omit [DecidableEq Y] in
lemma solar_motion (h:Green F)(hz:F 0=0) : jet (fun x=>(edgeM F x).det)=(motionJ (Z:=Y) (spool F)).det := by
  classical
  rw [solar_det (edge_green F h)];
  apply congrArg Matrix.det; ext1 i j
  exact (spool_ext F _ h hz _).symm

omit [DecidableEq Y] in
lemma edge_fder (x:Lawn (X⊕Y))(h:DifferentiableAt ℝ F x):
    (edgeM F x)=LinearMap.toMatrix' ((fderiv ℝ (fun s=>F (Sum.elim s (rightArm x))) (leftArm x)).toLinearMap) := by
  let A (s:Lawn X): Lawn (X⊕Y):=Sum.elim s (rightArm x)
  have hx : A (leftArm x)=x := funext fun j=> by cases j <;> rfl
  let L:= LinearMap.pi (Sum.elim (fun i:X=>LinearMap.proj (R:=ℝ) (φ:=fun _=>ℝ) i) (fun _:Y=>0)) |>.toContinuousLinearMap
  have hp : HasFDerivAt A L (leftArm x) := by
    -- use affine via linear shift
    let C: Lawn (X⊕Y):= Sum.elim (fun _=>0) (rightArm x)
    have he: A=fun z=> L z + C:= by funext z j; cases j with
                                      | inl i=> change _ = z i+0; rw [add_zero]; rfl
                                      | inr i=> change _=0+rightArm x i; rw [zero_add]; rfl
    rw [he]; exact L.hasFDerivAt.add_const C
  have hd := h.hasFDerivAt; rw [← hx] at hd
  have hi (i) : fderiv ℝ (fun p=> F p i) x = (ContinuousLinearMap.proj (φ:=fun _:X=>ℝ) i) ∘L fderiv ℝ F x := ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:X=>ℝ) i).hasFDerivAt.comp x h.hasFDerivAt).fderiv
  have he (j : X): L (Pi.single j (1:ℝ))= pebble (.inl j) := by
    funext a; cases a with
    | inl i=> change Pi.single (M:=fun _=>ℝ) j (1:ℝ) i = _; classical by_cases h:i=j <;> simp [pebble,h]
    | inr i=> change 0= _; classical simp [pebble]
  rw [show (fun s=>F (Sum.elim s (rightArm x)))=F ∘ A from rfl,(hd.comp (leftArm x) hp).fderiv,hx]; ext1 i j
  simp only [edgeM,rub,Matrix.of_apply,LinearMap.toMatrix'_apply,ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,hi]; rw [he]; rfl
omit [DecidableEq Y] in
lemma edge_det (x:Lawn (X⊕Y))(h:DifferentiableAt ℝ F x) : (edgeM F x).det=(fderiv ℝ (fun s=>F (Sum.elim s (rightArm x))) (leftArm x)).det := by rw [edge_fder _ x h, LinearMap.det_toMatrix']

end determinant
end YM.WilsonCoeffUV.Blue
