import YM.AlbaMS.Cutis.Go

/-!
# Based Stokes for formal Gaussian readings in all Fritzes resolving pairs

Works to prove exact insertions vanish on the Lagrangian. Does not integrate
any extensive scalar absolutely! Identity for Book.Size-high quadratic kernel
(continuum variants in symbolic form later). contact separation hypotheses only
if used with products; `cross`. Keep pure Tone on preimage for signs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap Matrix IsNilpotent
open scoped BigOperators Classical Topology Matrix
open Bric Coil Loft
variable {E B I R S : Type*} [Fintype E][Fintype B][CommRing R][Algebra ℚ R]
variable (F : Fritz E B R) (P : Lot E B R) (r:R)
namespace Fritz
-- full projection identities. `Fund` lacks positivity (only applicable assuming based)
structure Fund [DecidableEq E][DecidableEq B](P : Lot E B R)(F:Fritz E B R) : Prop where
  resonance : P.X*F.U.transpose+F.H*P.Z.transpose=1
  long : F.U.transpose*P.X=1
omit [Algebra ℚ R] in
lemma tribute [DecidableEq E][DecidableEq B] (h:Fund P F): F.handle P r= Strip.unity E B r:=by unfold handle Strip.unity; rw [h.resonance,h.long]
variable [DecidableEq E] [DecidableEq B]
omit [Algebra ℚ R] in
lemma holy (h:Fund P F) : (F.handle P r).footing=θ r:=by rw [tribute F P r h, Strip.universal]
-- print at rank zero. unnormalized
private def smite (p:Lot E B R)(r:R) : Module.End R (Floor E B R):= p.q r-touch (θ r) Finset.univ
lemma chills (h:Fund P F) {U:Floor E B R} (H:FinRank U): wither F.hop Finset.univ (smite P r U)= P.q r (wither F.hop Finset.univ U):=by
  let T:=touch (ρ:=ø) (θ (B:=B) (E:=E) r) Finset.univ
  have hF: FinRank (smite P r U):= ((FinRank.cross ⟨_, P.rank.cap _ _⟩ H) : FinRank (P.q r U)).sub H.touch
  have he: Commute T (touch F.hop Finset.univ):=by apply LinearMap.ext; intro i; exact touch_touch _ _ _ _ _ _ _ (Strip.work r) F.hopGrade -- equality fun
  have ht:reflects (smite P r) (-T) F.hop Finset.univ:=by intro Y; unfold smite; have hl:= F.lodges P r Y; rw [F.holy P r h] at hl; rw [LinearMap.sub_apply, LinearMap.sub_apply,map_sub]; rw [hl, show touch (θ r) Finset.univ (touch F.hop Finset.univ Y)=_ from LinearMap.congr_fun he Y]; abel
  have hc := reflects_wither ht he.neg_left H hF; change P.q r (wither _ _ _) - T (wither _ _ _) = _ + -T (wither _ _ _) at hc; rw [sub_eq_add_neg] at hc; exact (add_right_cancel hc).symm
omit [DecidableEq E][DecidableEq B] in
lemma cold (Y:Floor E B R): P.q r Y []=0:= by
  change tether _ _ _ _ _ []=_; rw [from_vectors _ (Strip.work r), tom_apply, sum_read]; apply Finset.sum_eq_zero; intro i _; rw [tap_mul, show cross true (θ r) Finset.univ P.combo (varC R ø i) []=0 from ?_, MulZeroClass.zero_mul]; change P.q r (varC R ø i) []=_; rw [kick,sum_read]; simp
-- normalized insertions think preimages, require exact yes Board `smite` corrected. lemma full
abbrev eval (f : Place E B→Place E B→ R)(U:Floor E B R):= wither f Finset.univ U []
-- all words. only even master interaction, ef.
variable {Y U : Floor E B R}
omit [DecidableEq E][DecidableEq B] in
lemma emit {u:Bool} (h : EvenT Y)(H:Tone u U)(hv:IsNilpotent Y)(hh:master_eff (P.q r) (θ r) Finset.univ Y=0):
    smite P r (exp (-Y)*U)= exp (-Y)* quantum (θ r) Finset.univ (P.combo+Y) U:=by
  let d:=touch (θ r)  (ρ:=@ø E B) Finset.univ; let T:= θ (E:=E) (B:=B) r; let s:Finset (Place E B):=Finset.univ; let A:=exp (-Y); let C (F G:Floor E B R):=cross true T s F G
  have ha : EvenT A:= h.neg.exponent
  have he:=master_rule (s:=Finset.univ) (U:=P.q r) h hv (Strip.work r) (cross_lev (Strip.work r) P.tone) -- lever orientation? U implicit need set
  have ht:C A U= -(A*C Y U):=by unfold C; rw [cross_flip ha H (Strip.work _),cross_exp h.neg H (Strip.work _) hv.neg,cross_flip H h.neg (Strip.work _)]; simp; rw [← from_tether,map_neg]; simp [A,T]
  have hb : smite P r (exp (-Y))=0:=by rw [hh] at he; exact he.trans (by simp)
  change P.q r (A*U)-d (A*U)= _
  have hf : P.q r (A*U)= P.q r A *U+A*P.q r U:= by change cross true _ _ _ (A*U)=_; rw [uses (Strip.work r) P.tone, ha.pl true, Bool.and_false,sting_false]; rfl
  rw [hf,show d (A*U)=_ from main_product_even (p:=true) ha]; change _- (d A*U+A*d U+ C A U)= A*(cross _ _ _ _ _-_); rw [ht]; rw [add_cross]; change P.q r A* U+A*P.q r U-(d A*U+A*d U+ -_)=A*(P.q r U+C Y U-d U);
  rw [show P.q r A=d A from sub_eq_zero.mp hb,mul_sub,mul_add]; abel
lemma exacts {b : Bool} (h:Fund P F)(hr:FinRank U)(H:Tone b U)(he:EvenT Y) (hn:IsNilpotent Y)(hp:FinRank Y)(hh:master_eff (P.q r) (θ r) Finset.univ Y=0) :
    eval F.hop (exp (-Y) * quantum (θ r) Finset.univ (P.combo+Y) U)=0:=by unfold eval; rw [← emit (P:=P) (r:=r) he H hn hh,chills F P r h (hp.neg.exponent.mul hr)]; exact cold P r _ -- order
end Fritz
end YM.MSBar.Cutis
