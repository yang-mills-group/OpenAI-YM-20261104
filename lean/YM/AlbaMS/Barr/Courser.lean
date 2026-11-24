import YM.AlbaMS.Barr.Shade
/-!
# tree drives out ghost and Haar stencils

Establish exact equalities after projection of action. Recipe applies to
various bases. Allows no tree adjacency proofs. Need for trivial-saddle reading.
No assumptions about registration f matching.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr.Axial
open Set Function Filter IsNilpotent LinearMap
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Odom Lattice Nexus Loft Cutis Cutis.Winter
variable {E I R S:Type*}[CommRing R][CommRing S] [DecidableEq E] {G:Gauge}
variable (T:Tune R){Ω:Net E I}(v:Finset E)(b:Bool){F:Heave G E I ℝ} {p:Bool}
variable [Fintype E][Fintype I]
def IdleNot (T:Tune R):Prop:= T.A=1 ∧ T.Gc=1
-- for vacuum rank2 using T and N.Wind at any slot.
omit [Fintype E][Fintype I] in
lemma mantle_w (A:R→+* S): mantel (G:=G) (I:=I) S b v=fun i=>A (mantel R b v i):= by
  funext i; rcases i with (i|i)|(i|i)<;> unfold mantel<;> simp only [Sum.elim_inl, Sum.elim_inr]<;> first|(split <;> simp)|simp
omit [Fintype E][Fintype I] [DecidableEq E] in
lemma baseUniform (h:IdleNot T) : T.loomT = fun i:Leaf G E I=> T.D ((Tune.baseT T.a T.ha).loomT i):=by
  funext i; rcases i with (i|i)|(i|i)<;> simp [Tune.loomT, Tune.baseT, h.1,h.2]
omit [Fintype E][Fintype I] in
lemma pass_up (n:ℕ)(F:Heave G E I ℝ): act v b (T.up n F)= T.up n (act v b F):=by
  unfold act Tune.up; rw [dualWeft, loomroom]; nth_rw 1 [mantle_w v b T.D];rw [← turnroom]
omit [Fintype E][Fintype I] in
lemma abates (F:Heave G E I ℝ): act v b (Wind _ T.D (Tune.kinetic T.a T.ha F)) = Wind _ T.D (Tune.kinetic T.a T.ha (act v b F)):= by
  unfold act; nth_rw 1 [mantle_w v b T.D]; rw [← turnroom]; simp only [Tune.kinetic]; rw [dualWeft, heldrank]
omit [DecidableEq E][Fintype E][Fintype I] in
lemma up_two (h:IdleNot T)(H:Heg 2 F): T.up 2 F= Wind _ T.D (Tune.kinetic T.a T.ha F):=by rw [Tune.up,Tune.kinetic,H.criterion,baseUniform T h, turnroom,loom_prec _ _ (show Heg 2 (Wind _ T.D F) from H.seep _ _), Nat.sub_self,pow_zero,one_smul] -- qualifier names
omit [Fintype E][Fintype I] in
def m_stim (T:Tune R)(F J:Heave G E I ℝ):= T.fuelT F J-Wind _ T.D (Tune.kinetic T.a T.ha F)
omit [Fintype E][Fintype I] in
lemma move (F J:Heave G E I ℝ): act v b (m_stim T F J)=m_stim T (act v b F) (act v b J):=by unfold m_stim Tune.fuelT; unfold act; simp_rw [map_sub]; rw [show weft _ _ = _ from pass_up T v b 2 F, show weft _ _=_ from pass_up T v b 0 J, show weft _ (Wind ø T.D (Tune.kinetic T.a T.ha F))=_ from abates T v b F] -- issue
omit [Fintype E][Fintype I] [DecidableEq E] in
lemma zero_spin (h:IdleNot T)(F J Y:Heave G E I ℝ)(H : Heg 2 Y): m_stim T (F+Y) J= m_stim T F J:=by -- J free
  unfold m_stim Tune.fuelT Tune.kinetic; simp_rw [Tune.up_add,map_add]; rw [up_two T h H]; unfold Tune.kinetic; abel

-- Simple identifies only A-variable readings. Both projections coincide.
omit [Fintype E][Fintype I] [DecidableEq E] in
lemma SimpleT.dk {F:Heave G E I R}(h: Loft.SimpleT F)(i: Flit G E): Loft.SimpleT (DA i F):=by
  have he (j:Leaf G E I)(hf:D j F=0): D j (DA i F)=0:=by unfold DA; rw [DD]; rw [hf,map_zero]; exact sting_zero _
  exact ⟨⟨fun j=>he _ (h.1.1 _), fun j=> he _ (h.1.2 _)⟩, fun j=> he _ (h.2 _)⟩
omit [Fintype E][Fintype I] in
lemma authentic (F:Heave G E I R)(h:Loft.SimpleT F): act v true F=act v false F:=by
  unfold act; ext l; induction l generalizing F with|nil=> rw [weft_nil, weft_nil]|cons i l ih=>
    rw [← D_read, ← D_read (F:=weft (mantel R false _) _), weftD, weftD]; rcases i with (i|i)|(i|i)
    · rw [smul_read, smul_read, ih _ (SimpleT.dk h i)]; rfl
    all_goals first|(rw [show D (Sum.inl (Sum.inr i)) F=0 from h.1.1 i]; simp)|(rw [show D (Sum.inr (Sum.inr i)) F=0 from h.1.2 i]; simp)|(rw [show D (Sum.inr (Sum.inl i)) F=0 from h.2 i]; simp)
lemma partS (F:Odom.Book Ω G): Heg 2 (act v true (F.main- bare F.toLuster.caseG)) ∧ act v false (F.main- bare F.toLuster.caseG)=0:=by
  unfold Odom.Book.main superb feeds; let W : Heave G E I ℝ:= bare F.toLuster.caseG; let Kk := ∑ i:Flit G E, Loft.K ℝ i* Loft.beam Ω.chat i; let Ll := ∑ i:Flit G I, Loft.L (E:=Flit G E) ℝ i* rod (grit G I) i
  rw [show bare F.toLuster.caseG+ Kk - Ll - W=Kk-Ll by change W+_ - _ - _=_; abel] -- expansion pattern
  have he (i:Flit G E)(a:Heave G E I ℝ) : act v false (Loft.K ℝ i*a)=0:=by unfold act; rw [weft_mul, Hvar]; simp [mantel,Place.k] -- issue
  have hl (b:Bool): act v b Ll=0:=by unfold act Ll; rw [map_sum]; apply Finset.sum_eq_zero; intro i _; rw [weft_mul, Hvar]; simp [mantel,Place.l]
  constructor
  · unfold act; rw [map_sub, show weft _ Ll=0 from hl true,sub_zero]; unfold Kk; rw [map_sum]; apply Heg.sum _ _; intro i _; rw [weft_mul,Hvar]; by_cases ht:i.1∈v; · unfold Loft.beam; rw [map_sum]; refine Heg.mul (n:=1) (m:=1) ((Heg.var _).smul _) ?_; apply Heg.sum _ _; intro j _; rw [weft_mul,Hvar, show weft _ (Ω.chat j i)=_ from zeroc v Ω i ht j]; exact Heg.mul (n:=1) ((Heg.var _).smul _) (Heg.put0 _)
    rw [show mantel ℝ true v (Place.k (B:=Flit G I) i)=0 from if_neg (fun h=>ht h.1),zero_smul,zero_mul];apply Heg.zero
  unfold act; rw [map_sub,show weft _ Ll=0 from hl false,sub_zero, show weft _ Kk = _ from map_sum (weft (mantel ℝ false v)) _ _]; exact Finset.sum_eq_zero fun i _=> he ..
-- use to realize μ annihilation equality against Ward's dormant reading
abbrev reed (F: Odom.Book Ω G)(T:Tune R):= m_stim T (bare F.toLuster.caseG) F.ash
lemma suum (F:Odom.Book Ω G)(h:IdleNot T): act v true (F.stim T) = act v false (reed F T):=by
  let A: Heave G E I ℝ:= bare F.toLuster.caseG; change act v true (m_stim T _ _)=_; rw [move]; rw [reed,move]; rw [← authentic v A (bare_simple _), ← authentic v F.ash (bare_simple _)]; nth_rw 1 [← sub_add_cancel F.main A]; -- need general zero_spin J
  rw [show F.main-A+A=A+(F.main-A) by abel]; unfold act; rw [map_add]; exact zero_spin T h _ _ _ (partS v F).1
end YM.MSBar.Barr.Axial
