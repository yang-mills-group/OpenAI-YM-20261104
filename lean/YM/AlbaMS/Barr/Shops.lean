import YM.AlbaMS.Barr.Bloom

/-! Coefficient comparisons after normalization. No explicit tree generator or values yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis.Fritz
open Set Function Filter LinearMap IsNilpotent
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Odom Lattice Nexus Loft
variable {E B R : Type*}[CommRing R][Algebra ℚ R][Fintype E][Fintype B](P:Lot E B R)(r:R)
variable (f:Place E B→Place E B→R)(F:Fritz E B R)(W U:Floor E B R)
-- W shares free quadratic through `Part` convention. NIL equipped requirement e choice.
def play (f:Place E B→Place E B→R) (W U:Floor E B R): R:= eval f (exp (-W)*U)
def gig (f:Place E B→Place E B→R)(W:Floor E B R): R:= play f W 1
def bought (f:Place E B→Place E B→R)(W:Floor E B R): Prop:= IsUnit (gig f W)
-- Ring.inverse totalizes
noncomputable def levy (f:Place E B→Place E B→R)(W U:Floor E B R): R:= Ring.inverse (gig f W)* play f W U
structure Align (P:Lot E B R)(W:Floor E B R)(r:R):Prop where
  tone : EvenT W
  nil : IsNilpotent W
  rank : FinRank W
  ambient : master_eff (P.q r) (θ r) Finset.univ W=0
-- don't burn upper coefficient loops for Member bracket algebra
abbrev Part := quantum (θ r) Finset.univ (P.combo+W)
variable {f} {T:Fritz E B R}
lemma part_one : Part P r W 1=0:=by rw [Part,quantum_apply,show cross true (θ r) Finset.univ (P.combo+W) 1=0 from cross_put_right (ρ:=ø) 1 (Strip.work r), touch_one,sub_self]
lemma part_need (h:FinRank W)(hh: FinRank U): FinRank (Part P r W U):= (((show FinRank P.combo from ⟨_, P.rank.cap _ _⟩).add h).cross hh).sub hh.touch
variable {U W}
lemma prize (h:bought f W) (U:Floor E B R): levy f W U * gig f W= play f W U:=by rw [levy,mul_right_comm,Ring.inverse_mul_cancel _ h,one_mul] -- order
lemma levy_one (h:bought f W): levy f W 1=1:= Ring.inverse_mul_cancel _ h
lemma act_lump (h:FinRank W)(he:FinRank U)(a:R): play f W (a • U)= a*play f W U:= by rw [play, mul_smul_comm,eval,wither_smul (h.neg.exponent.mul he)]; rfl
lemma act_leq (h:FinRank W)(he:FinRank U){V:Floor E B R}(H: FinRank V): play f W (U-V)= play f W U- play f W V:=by rw [play,mul_sub,eval,foe (h.neg.exponent.mul he) (h.neg.exponent.mul H)]; rfl
variable [DecidableEq E][DecidableEq B]
-- resonance witness orth supplies exact contraction primitive
variable {p:Bool}{P r F}
theorem shared (h:Align P W r)(hr:IsUnit r)(hi: T.Fund P)(H: F.Normal P)(he:EvenT U)(hp:FinRank U)(hv:Part P r W U=0) : play T.hop W U=play F.hop W U:=by
  apply anywhere P F r _ H T hi hr (h.rank.neg.exponent.mul hp) (h.tone.neg.exponent.mul he); · rw [show δ P r (exp (-W)*U)= _ from emit P r h.tone he h.nil h.ambient,hv,mul_zero]
lemma gign (h:Align P W r)(hr:IsUnit r)(hi:T.Fund P)(H:F.Normal P) : gig T.hop W=gig F.hop W:=shared h hr hi H Tone.one FinRank.one (part_one ..)
lemma gauge_neutral (h:Align P W r)(hr:IsUnit r)(hi:T.Fund P)(H:F.Normal P)(he:EvenT U)(hp:FinRank U)(hv:Part P r W U=0) : levy T.hop W U=levy F.hop W U:=by rw [levy,levy,shared h hr hi H he hp hv,gign h hr hi H]
lemma play_zero (h:Align P W r)(H:F.Fund P)(he:Tone p U)(hp:FinRank U): play F.hop W (Part P r W U)=0:= exacts F P r H hp he h.tone h.nil h.rank h.ambient
lemma levy_zero (h:Align P W r)(H:F.Fund P)(he:Tone p U)(hp:FinRank U): levy F.hop W (Part P r W U)=0:=by rw [levy,play_zero h H he hp,mul_zero]
-- fundamental: normalized when unit supplied. gauge-invariant (not all unphysical) transports. no budget.
lemma classifies (h:Align P W r)(H:F.Normal P)(hr:IsUnit r)(he:bought F.hop W)(hp:FinRank U)(hh: EvenT U)(hv:Part P r W U=0):
    ∃ S:Floor E B R, FinRank S ∧ OddT S ∧ U-levy F.hop W U • 1 = Part P r W S:=by
  let e:=exp (-W); let c:=levy F.hop W U; let L:= U-c • 1; have hx : e*(exp W)=1:= exp_neg_mul_exp_self h.nil; have ht : FinRank L:= hp.sub (FinRank.one.smul _); have hl : EvenT L:=hh.sub (Tone.one.smul _)
  have hxU:δ P r (e*L)=0:=by rw [show δ P r (e*L)= _ from emit P r h.tone hl h.nil h.ambient]; unfold L; rw [show quantum _ _ _ (_-_ : Floor E B R)=_ from map_sub (Part P r W) _ _]; rw [hv,map_smul,part_one, smul_zero,sub_self,mul_zero]
  have ha : eval F.hop (e*L)=0:=by change play F.hop W (_-_)=0; rw [act_leq h.rank hp (FinRank.one.smul _), act_lump h.rank FinRank.one, show c*play F.hop W 1=_ from prize he U,sub_self]
  obtain ⟨S,hs,hS,hb⟩:= weld P F r (e*L) H hr (h.rank.neg.exponent.mul ht) (show EvenT _ from h.tone.neg.exponent.mul hl) hxU ha
  have hsX:OddT (exp W*S):= h.tone.exponent.mul hS; refine ⟨exp W*S,h.rank.exponent.mul hs, hsX,?_⟩
  apply (show IsUnit e from isUnit_exp h.nil.neg).mul_left_cancel; change e*L = _; rw [← show δ P r (e*(exp W*S))= _ from emit P r h.tone hsX h.nil h.ambient, ← mul_assoc,hx,one_mul]; exact hb
lemma classify_leads (h:Align P W r)(H:F.Fund P)(he:bought F.hop W) (S:Floor E B R)(a:R)(hp:FinRank U)(hs:FinRank S)(hy:Tone true S)(hv:U-a • 1=Part P r W S) : levy F.hop W U=a:=by
  have ht:=play_zero h H hy hs; rw [← hv, act_leq h.rank hp (FinRank.one.smul a),sub_eq_zero,act_lump h.rank FinRank.one] at ht; refine IsUnit.mul_right_cancel he ?_; rw [prize he]; exact ht
end YM.MSBar.Cutis.Fritz
