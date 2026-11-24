import YM.AlbaMS.Barr.Courser

/-! # identity of tree diagram prescription to based gauge & normalized

This is an actual axial prescription including orbit lift. No reference to any
continuum term. Use with Physical stencil (s) satisfying `Closed`, may include
additive bare sum. Needs correct parameter uses. Doesn't require checking
summand components after quantum prep; uses total F. Eq real stencils whole.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr.Axial
open Set Function Filter IsNilpotent Matrix
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Odom Lattice Nexus Loft Cutis Cutis.Winter
variable {E I R:Type*}[Fintype E][Fintype I][CommRing R][Algebra ℚ R]{G:Gauge}{n:Side}{A:Precision.ChartRatio G}
lemma weft_wither (Z:Place E I→R)(u:Floor E I R)(h:FinRank u){P T:Place E I→Place E I→R}(H:∀ i j, P i j*Z i*Z j=T i j): Fritz.eval P (weft Z u)= Fritz.eval T u:=by
  let N:=h.choose; unfold Fritz.eval; rw [withers (h.choose_spec.weft Z) (by omega : N≤2*N),withers h.choose_spec (by omega : N≤2*N),twig_apply,twig_apply,sum_read,sum_read];
  have hh (F:Floor E I R): touch P Finset.univ (weft Z F)= weft Z (touch T Finset.univ F):= by rw [weft_touch (r:=1) (g:=T) Z (fun i j=> by rw [H, MulOneClass.one_mul]),one_smul]
  refine Finset.sum_congr rfl fun i _=> ?_; rename_i hi; clear hi; simp only [pe_apply,smul_read]; congr 1;
  suffices ∀ (F:Floor E I R), (touch P Finset.univ ^i) (weft Z F)= weft Z ((touch T Finset.univ ^i) F) by rw [this,weft_nil]
  induction i with|zero=>intro F;rfl|succ i ih=> intro F; simp_rw [pow_succ',Module.End.mul_apply,ih,hh]

-- official axial observation. W constructed from energy alone with chart spin, pin Wlp from same θ. covariance excludes ALL K,c,L. variables restricted tree. no scale compensation.
namespace Window
variable (T:Tune R)(hp:Precision.LocalRatio A)(P:Window n)
-- use orientation
abbrev StoneX (G:Gauge)(n:Side)(R:Type*)[CommRing R]:= Heave G (Foil n) (Nail n true) R
def mix : Fritz (Env G n) (Sand G n) R:= (P.safeCov hp T.a).replic T.D
def own : Fritz (Env G n) (Sand G n) R:= { mix T hp P with U:=0 }
def stump : StoneX G n R:= act P.s false (reed (Root G A n true hp) T)
-- restrict also inputs separately
noncomputable def Proper (U:StoneX G n R): R:= Fritz.levy (own T hp P).hop (stump T hp P) (act P.s false U)
variable {T}{P}
private lemma shield (i:Env G n)(j:Env G n)(h:Even n.val) : (mix T hp P).hop (Place.a i) (Place.a j) * mantel R false P.s (Place.a (B:=Sand G n) i) * mantel R false P.s (Place.a (B:=Sand G n) j)= (mix T hp P).hop (Place.a i) (Place.a j):=by
  have he (i:Env G n)(hi:i.1∈P.s)(j:Env G n) : (mix T hp P).H i j=0:=by change T.D ((P.safeCov hp T.a).H i j)=0; rw [P.peg_to hp i h T.ha hi j,map_zero]
  change (_ * (mix T hp P).H i j) * (if i.1∈P.s then 0 else 1) * (if j.1∈P.s then 0 else 1)= _ * (mix T hp P).H i j
  by_cases hi:i.1∈P.s; simp [he i hi j]
  by_cases hj:j.1∈ P.s; rw [(mix T hp P).symm i j]; simp [he j hj i]; simp [hi,hj]
omit [Algebra ℚ R] in
private lemma shade (i:Env G n)(j:Sand G n)(h:Even n.val): (mix T hp P).U i j* mantel R true P.s (Place.k (B:=Sand G n) i)= (mix T hp P).U i j:=by
  unfold mantel Place.k; dsimp only [Sum.elim_inl, Sum.elim_inr]; by_cases h':i.1∈P.s; simp [h']; rw [show (mix T hp P).U i j=T.D _ from rfl,P.root_to hp i h T.ha h' j,map_zero]; simp

lemma EPcore (h:Even n.val) (F:StoneX G n R)(hf:FinRank F): Fritz.eval (mix T hp P).hop (act P.s true F)=Fritz.eval (mix T hp P).hop F:= by
  apply weft_wither _ F hf; rintro ((i|i)|(i|i)) ((j|j)|(j|j))
  all_goals first | exact shield (T:=T) (P:=P) hp i j h | (solve|simp [Fritz.hop,Fritz.rose,mantel]) | skip -- overhead
  -- K,C and C,K
  · change _ * -(mix T hp P).U i j * _* 1=_; rw [mul_one, mul_neg, neg_mul, _root_.mul_assoc, shade hp _ _ h]; exact (mul_neg ..).symm -- inspect
  change halve R * (mix T hp P).U j i * 1 *_=_; rw [mul_one,_root_.mul_assoc]; rw [shade hp j i h]; rfl
lemma EPbare (h:Even n.val) (F:StoneX G n R)(hf:FinRank F): Fritz.eval (mix T hp P).hop (act P.s false F)=Fritz.eval (own T hp P).hop F:=by
  apply weft_wither _ F hf; rintro ((i|i)|(i|i)) ((j|j)|(j|j))
  all_goals first| exact shield hp i j h| simp [own,Fritz.hop, Fritz.rose,mantel]
omit [Algebra ℚ R] in
lemma idol (s:Finset (Foil n))(X:StoneX G n R) : act s false (act s false X)=act s false X:=by apply run_weft _ _ _ _; rintro ((i|i)|(i|i)); all_goals first|(simp only [mantel]; cases Decidable.em (i.1∈s) <;> simp [*])|simp [mantel] -- fix rfl
lemma common (h:Even n.val)(hP:IsNilpotent ((Root G A n true hp).stim T))(hb:IsNilpotent T.z)(hT:IdleNot T)
    {U:StoneX G n R}(u:Loft.SimpleT U)(hr:FinRank U): Fritz.play (mix T hp P).hop ((Root G A n true hp).stim T) U=
    Fritz.play (own T hp P).hop (stump T hp P) (act P.s false U):=by
  let X:= Root G A n true hp; let W:= X.stim T; let E:= exp (-W); let B:= stump T hp P
  have ht: act P.s true W=B:= suum T P.s X hT
  have hv: IsNilpotent B:= ht ▸ hP.map (SumB (mantel R true P.s)) -- defeq
  have hs := X.stim_rank T hb
  have hf:FinRank B:=ht ▸ show FinRank (act P.s true W) from ⟨_,hs.choose_spec.weft _⟩
  unfold Fritz.play; rw [← EPcore hp h _ (hs.neg.exponent.mul hr),← EPbare hp h _ (hf.neg.exponent.mul ⟨_,hr.choose_spec.weft _⟩)]
  congr 1; change act P.s true (E*U)=act P.s false (exp (-B)*act P.s false U); unfold act; rw [weft_mul,weft_mul,show weft _ (weft _ U)= _ from idol P.s U, show weft _ U= _ from authentic P.s U u]; unfold E; rw [SumB_exp _ _ hP.neg, SumB_exp _ _ hv.neg,map_neg,map_neg]; rw [show weft _ _=B from ht]; rw [show weft _ B=B from idol P.s (reed X T)] -- specify
lemma spline (h: Even n.val)(hP:IsNilpotent ((Root G A n true hp).stim T))(hb:IsNilpotent T.z)(hT:IdleNot T)
    {U:StoneX G n R}(u:Loft.SimpleT U)(hr:FinRank U)(H:quantum T.bracket Finset.univ ((Root G A n true hp).charter T) U=0)(hu:EvenT U):
    Proper T hp P U= Salute.standard T hp U:=by
  have ht : Fritz.gig (mix T hp P).hop ((Root G A n true hp).stim T)= Fritz.gig (own T hp P).hop (stump T hp P):=by
    have he:=common (T:=T) (P:=P) hp h hP hb hT (U:=1) (by constructor; constructor; all_goals exact fun _=> D_one (R:=R) _) FinRank.one; rw [show act P.s false (1:StoneX G n R)=1 from Barr.one_on _] at he; exact he
  unfold Proper; unfold Fritz.levy; rw [← common (P:=P) hp h hP hb hT u hr,← ht];
  have hd:=(P.safe_core hp h T.ha); let Q:=phys (Root G A n true hp) T.a; let V:= P.safeCov hp T.a; have he: (mix T hp P).Fund (locate T hp):= {
    resonance:= by change Q.X.map T.D * (V.U.map T.D)ᵀ+V.H.map T.D*(Q.Z.map T.D)ᵀ=_; rw [← transpose_map, ← transpose_map,← Matrix.map_mul,← Matrix.map_mul, ← Matrix.map_add T.D (map_add T.D), show Q.X*V.Uᵀ + V.H*Q.Zᵀ=1 from hd.resonance,Matrix.map_one _ T.D.map_zero T.D.map_one]
    long:= by change (V.U.map T.D)ᵀ*Q.X.map T.D=_; rw [← transpose_map,← Matrix.map_mul,show V.Uᵀ*Q.X=1 from hd.long,Matrix.map_one _ T.D.map_zero T.D.map_one] }
  apply Fritz.gauge_neutral (P:=locate T hp) (F:=drive T (n:=n) (G:=G)) (r:=Salute.total T) (Salute.legal T _ hP hb) (Salute.isRoot T) he (Rosetta hp h T) hu hr -- maybe apply creates noise
  change Fritz.Part (Salute.planeBook T _) (Salute.total T) _ U=0; rw [Salute.bridge]; exact H
end Window
end YM.MSBar.Barr.Axial
