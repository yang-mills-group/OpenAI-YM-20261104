import YM.AlbaMS.Cutis.Resolver

/-!
# Book kinetic basis

Recover derivatives in columns without choosing rank tensor equivalences.
Proof uses ordinary matrices only when transferring through global scalings
and Net.Receipt to specialized Stamp. Exact consistency.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap
open scoped BigOperators Classical Topology Matrix
open Bric Coil Loft Odom Inlay Inlay.Net
variable {E B I R S : Type*} [Fintype E][Fintype B][CommRing R][Algebra ℚ R][CommRing S][Algebra ℚ S]
-- native frame and physical temperature shift
namespace Lot
variable (P:Lot E B R)(r t:R)(K:R→+*S)
omit [Algebra ℚ R][Fintype E][Fintype B] in
def scale (r t:R): Lot E B R where
 Z:= r • P.Z
 X:= t • P.X
 symm i j:=by rw [Matrix.smul_apply, Matrix.smul_apply, P.symm i j]

omit [Fintype E][Fintype B][Algebra ℚ R][Algebra ℚ S] in
def beam : Lot E B S:= ⟨P.Z.map K,P.X.map K,fun i j=> congr_arg K (P.symm i j)⟩
lemma beacon : (P.beam K).combo= Wind ø K P.combo := by
  have ht (i:Place E B): Wind ø K (varC R ø i)=varC S ø i:=by ext l; by_cases h:l=[i] <;> simp [blows,seep_read,var_read,h]
  unfold combo boson tong; rw [map_add]; simp_rw [Wind_smul,map_sum,Wind_smul,map_mul, Loft.K,C,A,ht]; rw [halve_unique]; rfl
lemma markScale : (P.scale r t).combo=r • P.boson+t • P.tong:=by
  unfold combo boson tong scale; rw [smul_comm r]; simp_rw [Matrix.smul_apply,smul_eq_mul, ← smul_smul, Finset.smul_sum] -- orientation
omit [Fintype E] [Fintype B] [Algebra ℚ R] in
lemma Z_sym : P.Z.transpose=P.Z:= Matrix.ext fun i j=> P.symm j i
lemma bookA (x y:E): DA y (DA x P.combo) = put ø (P.Z x y):=by
  rw [P.combo_A, map_sum, Finset.sum_eq_single y]; rw [map_smul]; simp only [DA,A,varD,if_true,← put_smul_left,mul_one]; intro i _ hi; rw [map_smul]; simp [DA,A,Place.a,Ne.symm hi]; simp
lemma bookD (x:E)(y:B): DC y (DK x P.combo)=put ø (P.X x y):=by
  rw [P.combo_K,map_sum, Finset.sum_eq_single y]; rw [map_smul]; simp only [DC,C,varD,if_true,← put_smul_left,mul_one]; intro i _ hi; rw [map_smul]; simp [DC,C,Place.c,Ne.symm hi]; simp
end Lot
-- real-native Book connectors. Hess just before period. Keep projection proof rank two on minimal needs.
section net
variable {G : YM.Gauge}{Ω:Net E B}(F:Odom.Book Ω G)(P:Tune R)
abbrev OB:= Lot (Flit G E) (Flit G B)
def waveLots: OB (G:=G) (E:=E) (B:=B) ℝ where
  Z:= Matrix.of fun i j=> F.main [Place.a i,Place.a j]
  X:= Matrix.of fun i j=> Ω.chat j i []
  symm i j:= F.main.trusted [] [] (Place.a i) (Place.a j)
-- alternatively read from bare field hessian (tong contributes nothing)
lemma phi_sweep (i:Flit G E): DA i ((waveLots F).tong)=0:= by simp [DA,Lot.tong,mulD,Loft.K,C,Place.k,Place.a,Place.c]
lemma bodyN : rankn 2 F.main= (waveLots F).combo:= by
  let P:=(waveLots F); let V:= F.toLuster.caseG
  have he : rankn 2 F.main= rankn 2 (bare V) +P.tong:= by
    unfold Lot.tong; change rankn 2 (superb _ _ (bare V))= _; rw [sea]; simp_rw [← grid (Ω:=Ω), Finset.mul_sum, mul_smul_comm]; rfl
  rw [he, Lot.combo]
  suffices h : rankn 2 (bare (I:=B) V)=P.boson by rw [h]
  let A:=bare (I:=B) V; let Q:=rankn 2 A
  have hv:Heg 2 P.boson:= (Heg.sum _ _ (fun x _=> Heg.sum _ _ (fun y _=> ((Heg.var (R:=ℝ) (ρ:=ø) (Place.a x)).mul (Heg.var (Place.a y))).smul _))).smul _
  have hz (x y: Flit G E): Q [Place.a x,Place.a y]=P.boson [Place.a x,Place.a y]:=by
    let l:List (Leaf G E B):=[Place.a x,Place.a y]; have hh:P.tong l=0:= DFunLike.congr_fun (phi_sweep F x) [Place.a y]
    have hf:(rankn 2 F.main) l=F.main l:=by simp [l,rankn_read]
    rw [he,plus_read,hh,add_zero] at hf; refine hf.trans ?_; have hy:P.combo l=P.Z x y:= DFunLike.congr_fun (P.bookA x y) []; rw [Lot.combo,plus_read,hh,add_zero] at hy; exact hy.symm
  have hd : SimpleT P.boson:= ⟨⟨fun i=>by simp [DK,Lot.boson,mulD,Loft.A,Place.a,Place.k], fun i=>by simp [DL,Lot.boson,mulD,Loft.A,Place.a,Place.l]⟩,fun i=> by simp [DC,Lot.boson,mulD,Loft.A,Place.a,Place.c]⟩
  have hQ:SimpleT Q:=by
    have hc:= bare_simple (I:=B) V; have hy : ∀ i, D i A=0 → D i Q=0:=by intro i hi; unfold Q; rw [show 2=1+1 from rfl,D_rank,hi,map_zero]
    exact ⟨⟨fun _=> hy _ (hc.1.1 _), fun _=> hy _ (hc.1.2 _)⟩,fun _=>hy _ (hc.2 _)⟩
  have hn (x y:Leaf G E B) : (¬ ∃ i, x=Place.a i) → Q [x,y]=0 ∧ P.boson [x,y]=0:=by
    intro hn; have ht (A:Heave G E B ℝ)(h:SimpleT A): A [x,y]=0:=by
      rcases x with (x|x)|(x|x); exact False.elim (hn ⟨_, rfl⟩); exact DFunLike.congr_fun (h.1.1 x) [y]; exact DFunLike.congr_fun (h.2 x) [y]; exact DFunLike.congr_fun (h.1.2 x) [y];
    exact ⟨ht Q hQ,ht P.boson hd⟩
  ext l; by_cases h:l.length=2
  · rcases l with _|⟨x,_|⟨y,_|_⟩⟩<;> simp only [List.length_nil,List.length_cons] at h <;> try omega -- keep middle
    by_cases ht:∃ i,x=Place.a i
    · obtain ⟨i,rfl⟩:=ht; by_cases ht:∃ i,y=Place.a i
      · obtain ⟨j,rfl⟩:=ht; exact hz i j
      have hr : Q [y,Place.a i]= P.boson [y,Place.a i]:=(hn y _ ht).1.trans (hn y _ ht).2.symm
      exact (Q.trusted [] [] (Place.a i) y).trans ((congr_arg _ hr).trans (P.boson.trusted [] [] (Place.a i) y).symm)
    exact (hn x _ ht).1.trans (hn x _ ht).2.symm
  rw [rankn_read, if_neg h]; exact (not_not.1 (mt (hv l) h)).symm
end net
end YM.MSBar.Cutis
