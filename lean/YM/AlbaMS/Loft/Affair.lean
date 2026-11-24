import YM.AlbaMS.Loft.Terminal

/-!
# Squaring minimal generator

Take field motion from chart generators `z[j,i]`: each gauge direction j has
the vector fields z_{j,i} in the even variables. Actual context applies using
the G-chart at arbitrary selected orbit. Prove unimodularity contribution as
well, so no rankless term dropped without regulator. No Lie hypotheses on
z other than the actual representation equations -- no module
instance required for ghosts for using true gauge algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Loft
open Set Function Finset Bric Coil
open scoped BigOperators Classical
variable {E B R : Type*} [CommRing R] [Algebra ℚ R] [Fintype E] [Fintype B]
structure Codes (B R : Type*) [Fintype B] [CommRing R] where
  price : B → B → B → R
  skew x y z : price x y z= - price y x z
  Jac x y z i : (∑ j:B,price x y j*price j z i)+(∑ j:B, price y z j*price j x i)+(∑ j:B, price z x j*price j y i)=0
  tr x y : price x y y=0 -- real orthonormal Lie basis, explicit
variable (S : Codes B R)(z : B→E→Floor E B R)
def beam (i:E): Floor E B R:=∑ j:B, C R j*z j i
def rod (j:B): Floor E B R:= - halve R • ∑ x:B,∑ y:B, S.price x y j • (C R x*C R y)
-- Signs tested: left ∆ basis. odd field sign. `tr` not sign assumption.
omit [Fintype E] in
lemma certified (h : ∀ i j, EvenT (z i j)) (t : ∀ i j, SimpleT (z i j)): ConsoleF (beam z) (rod S) where
  jazz i:= Tone.sum _ _ fun j _=> (show OddT (E:=E) (C R j) from var_tone (ρ:=ø) (Place.c j)).mul (h j i)
  hue _:= Tone.smul (p:=false) (Tone.sum _ _ (fun x _=> Tone.sum _ _ fun y _=> Tone.smul ((show OddT (E:=E) (C R x) from var_tone (Place.c x)).mul (var_tone (ρ:=ø) (Place.c y))) _)) _ -- fix
  lean i:= Under.sum _ (fun j _=> (Under.c j).mul (t j i).1)
  strip i:= (Under.sum _ (fun j _=> Under.sum _ fun k _=> ((Under.c j).mul (Under.c k)).smul (S.price j k i))).smul _
abbrev impulse (j:B) (F : Floor E B R):= ∑ i:E,z j i* DA i F
abbrev sap := expandFloor (beam z) (rod S)
omit [Algebra ℚ R] in
lemma motive (F : Floor E B R): (∑ i:E, beam z i * DA i F)=∑ j:B,C R j* impulse z j F:=by unfold beam impulse; simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]; rw [Finset.sum_comm]
lemma motor (F : Floor E B R)(h : ∀ j, DC j F=0) : sap S z F=∑ j:B,C R j* impulse z j F:=by rw [sap,expands,motive]; simp [h]
omit [Fintype E] [Fintype B] [Algebra ℚ R] in
lemma swapC (x y : B): (C (E:=E) R x)*C R y=-(C (E:=E) R y*C R x):=(var_tone (ρ:=ø) (Place.c (E:=E) x)).commute (var_tone (Place.c y)) -- fix
private lemma one_rod (t : ∀ i j, SimpleT (z i j))(i:E)
    (H:∀ x y, (impulse z x (z y i))-(impulse z y (z x i))=∑ j:B,S.price x y j • z j i):
    (∑ j:B, rod S j*z j i) + ∑ x:B,plane true (C R x)*(sap S z (z x i))=0:=by
  let Q x y:=(C (E:=E) R x*C R y)*impulse z x (z y i)
  let L:=∑ x:B, ∑ y:B,Q x y
  have hz : (∑ x:B, plane true (C R x)*(sap S z (z x i)))= L:=by
    unfold L Q; rw [Finset.sum_comm (s:= (Finset.univ : Finset B)) (t:= (Finset.univ : Finset B)) (f:=fun x y=>_* impulse z x (z y i))] -- fix
    refine Finset.sum_congr rfl fun x _=>?_ ; rw [motor _ _ _ (t x i).2,(var_tone (ρ:=ø) (Place.c x)).pl true]; change -(C _ _)* _=∑ y:B,(C _ _*C _ _)*_; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _=>?_ ; rw [neg_mul,← mul_assoc, swapC,neg_mul,neg_neg] -- test
  rw [hz, ← twice_halve L];
  suffices ∑ j:B, rod S j * z j i = - halve R • (L+L) by rw [this,neg_smul,neg_add_cancel]
  simp_rw [rod,smul_mul_assoc,Finset.sum_mul,smul_mul_assoc, ← Finset.smul_sum]; congr 1
  rw [Finset.sum_comm]
  have h (x:B) : (∑ j:B,∑ y:B, S.price x y j • (C R x*C R y*z j i))=∑ y:B,(Q x y+Q y x):=by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _=>?_ ; simp_rw [← mul_smul_comm,← Finset.mul_sum,← H]
    rw [mul_sub]; unfold Q; nth_rw 2 [swapC (R:=R) (E:=E) x y]; rw [neg_mul,sub_neg_eq_add]
  simp_rw [h,Finset.sum_add_distrib]; rw [Finset.sum_comm (f:=fun x y=> Q y x)]
lemma one_beam (h : ∀ i j, EvenT (z i j))(t : ∀ i j, SimpleT (z i j)) (i:E)
    (H:∀ x y, impulse z x (z y i)-impulse z y (z x i)=∑ j:B,S.price x y j • z j i): sap S z (beam z i)=0:=by
  have hu:=certified S z h t
  unfold beam; -- also sap not unfolded; keep
  simp_rw [map_sum, sap, likes (beam z) (rod S) hu.jazz hu.hue, symbol_C, Finset.sum_add_distrib]; exact one_rod S z t i H

omit [Fintype E] in
lemma rodD (x y : B): DC x (rod (E:=E) S y)=-(∑ j:B,S.price x j y • C (E:=E) R j):= by
  have he (i j:B) : DC x (C R i*C (E:=E) R j)= ite (x=i) (C R j) 0 - ite (x=j) (C R i) 0 := by
    change D _ (_*_)=_; rw [mulD]; change _* _ + plane true (C _ _)*_= _; rw [(show OddT (E:=E) (C R i) from var_tone (Place.c i)).pl]; change _ * _ + -(C R i)*_=_; by_cases h:x=i<;> by_cases t:x=j<;> simp [C,h,t,Place.c,sub_eq_add_neg] <;> (split_ifs <;> simp)
  have hu : (∑ i:B,∑ j:B,S.price i j y • DC x (C R i*C (E:=E) R j))=(∑ j:B,S.price x j y • C R j)+(∑ j:B,S.price x j y • C R j):=by
    have ht (i j:B) (r:R) (v : Floor E B R) : r • (ite (i=j) v 0)=ite (i=j) (r • v) 0:=by by_cases h:i=j<;>simp [h]
    simp_rw [he,smul_sub,ht,Finset.sum_sub_distrib]; rw [Finset.sum_comm]; simp -- fix
    simp_rw [S.skew _ x, neg_smul,Finset.sum_neg_distrib, sub_neg_eq_add]

  unfold rod; rw [map_smul,map_sum]; simp_rw [map_sum,map_smul]; rw [hu,neg_smul,twice_halve]

omit [Fintype E] in
lemma rodDiv (x : B): DC x (rod (E:=E) S x)=0:= by simp_rw [rodD, S.skew x]; simp [S.tr]
omit [Fintype E] in
lemma rodA (x:E)(y:B): DA x (rod S y)=0:= by simp [DA,rod,mulD,C,Place.a,Place.c]

omit [Fintype B] [Fintype E] [Algebra ℚ R] in
private lemma cyclic (u v w:B) : C R u*C R v*C (E:=E) R w=C R v*C R w*C R u:= by rw [mul_assoc,(show EvenT (E:=E) (C R v*C R w) from (var_tone (R:=R) (ρ:=ø) (Place.c v)).mul (var_tone (ρ:=ø) (Place.c w))).slider]; rfl
lemma two_beam (i:B) : sap S z (rod S i)=0:=by
  have ha : (∑ u:E, beam z u*DA u (rod S i))=0:=by simp_rw [rodA]; simp
  let W (x y z:B):= C R x*C R y*C (E:=E) R z
  let Q x y z:=(∑ j:B,S.price x y j*S.price j z i) • W x y z; let M:=∑ x:B,∑ y:B,∑ z:B,Q x y z
  have he: (∑ j:B, rod S j* DC (E:=E) j (rod S i))=halve R • M:=by
    have hu x j:(-halve R • x) * -(∑ y:B, S.price j y i • C (E:=E) R y)=∑ y:B,halve R • (S.price j y i • (x*C R y)):=by rw [← Finset.smul_sum]; simp_rw [← mul_smul_comm,← Finset.mul_sum,neg_smul,neg_mul_neg,smul_mul_assoc]
    simp_rw [rodD,rod, hu,Finset.sum_mul, Finset.smul_sum, smul_mul_assoc, smul_smul]
    -- promote j to innermost, v(=c slot ending commutator) to just before j
    have ht (f:B→B→B→B→Floor E B R): (∑ j:B,∑ v:B,∑ x:B,∑ y:B,f x y v j) = ∑ x:B,∑ y:B,∑ v:B,∑ j:B,f x y v j:= by
      simp_rw [Finset.sum_comm (f:=fun v x=> ∑ y:B, f x y v _)]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _=>?_ ; simp_rw [Finset.sum_comm (f:=fun v y=> f x y v _)]; rw [Finset.sum_comm]; simp_rw [Finset.sum_comm (f:=fun j v=> f x _ v j)]
    simp_rw [← smul_smul (halve R), ← Finset.smul_sum]; congr 1
    unfold M Q; simp_rw [Finset.sum_smul]; rw [ht (fun (x y z j:B)=> (S.price j z i*S.price x y j) • W x y z)] -- pattern?
    exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> by rw [mul_comm]

  rw [sap,expands,ha,zero_add,he]
  have ht (f:B→B→B→Floor E B R) : (∑ x:B,∑ y:B,∑ z:B,f x y z)=∑ x:B,∑ y:B,∑ z:B,f y z x:= by simp_rw [Finset.sum_comm (f:=fun y z=> f _ y z)]; rw [Finset.sum_comm]
  have hx: M+M+M=0:=by
    unfold M; nth_rw 2 [ht]; nth_rw 3 [ht]; -- test
    nth_rw 2 [ht (fun x y z=> Q y z x)]; simp_rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro x _; apply Finset.sum_eq_zero; intro y _; apply Finset.sum_eq_zero; intro v _; dsimp only [Q,W]; rw [← cyclic (R:=R) (E:=E) y v x,← cyclic (R:=R) (E:=E) x y v, ← add_smul,← add_smul,S.Jac,zero_smul] -- transitions
  rw [show M=0 from ?_,smul_zero]
  letI : Module ℚ (Floor E B R):= Module.compHom (Floor E B R) (algebraMap ℚ R) -- check exists
  apply (smul_eq_zero_iff_right (M:=Floor E B R) (show (3:ℚ)≠0 by norm_num)).1; rw [show (3:ℚ)=1+1+1 from by norm_num,add_smul,add_smul,one_smul,hx] -- fix typeclass issue
omit [Algebra ℚ R] [Fintype E] in
lemma beamD (i:E)(j:E) : DA i (beam z j)=∑ x:B,C R x*DA i (z x j):= by simp [beam,map_sum,C,DA,mulD,Place.a,Place.c,show ø (Sum.inl (Sum.inl i) : Place E B)=false from rfl]

def superb (F:Floor E B R):= feeds (beam z) (rod S) F
structure Panel (z : B → E → Floor E B R)(F J : Floor E B R) : Prop where
  clear (x i) : EvenT (z x i)
  simple (x i) : SimpleT (z x i)
  evenF : EvenT F
  simpleF : SimpleT F
  evenJ : EvenT J
  simpleJ : SimpleT J
  law (x y i): impulse z x (z y i)-impulse z y (z x i)=∑ j:B,S.price x y j • z j i
  preserves x : impulse z x F=0
  measure x : (∑ i:E, DA i (z x i)) = - impulse z x J
namespace Panel
variable {F J : Floor E B R}{S z} (h: Panel S z F J)
include h
lemma tone : EvenT (superb S z F):= (certified S z h.clear h.simple).emits h.evenF
lemma top : ConsoleF.CMaster (oriented R) (superb S z F)=0:= (certified S z h.clear h.simple).top h.evenF h.simpleF.1
    (by change sap S z F=0; rw [motor S z F h.simpleF.2]; simp [h.preserves _]) (fun x=> one_beam S z h.clear h.simple x fun j k=>h.law j k x) (two_beam S z)
lemma height : delta (superb S z F)= -coupling (superb S z F) J:=by
  have he:=certified S z h.clear h.simple
  rw [superb, he.height h.simpleF.1, he.surf h.evenF h.simpleF.1 h.simpleJ.1, show expandFloor (beam z) (rod S) J=sap S z J from rfl, motor _ _ _ h.simpleJ.2]; simp_rw [beamD,rodDiv]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, h.measure, mul_neg]; simp [Finset.sum_neg_distrib]
end Panel
end YM.MSBar.Loft
