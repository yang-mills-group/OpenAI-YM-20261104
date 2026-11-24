import YM.AlbaMS.Cutis.Light
/-!
# Transport formula for standard Landau kernels

Computes actual free master comm for a one-line contraction, not indexing via
Orth~. Same on ℂ/etc with non-symmetric resolvers (sym=H only on A-part). No
convertibility with MS assumed. Ghost covariance sign as documented; Delta
with pointers. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap IsNilpotent
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Loft
variable {E B I R S : Type*} [Fintype E][Fintype B][CommRing R][Algebra ℚ R]
structure Fritz (E B R : Type*) where
  H : Matrix E E R
  U : Matrix E B R -- C(K,c) is minus U
  symm i j : H i j= H j i
namespace Fritz
variable (F:Fritz E B R) (P:Lot E B R)(r:R)
def rose : Place E B→Place E B→ R
| .inl (.inl i),.inl (.inl j)=> F.H i j
| .inl (.inr i),.inr (.inl j)=> - F.U i j
| .inr (.inl j),.inl (.inr i)=> F.U i j
| _,_=>0
-- uses pair entries only!
abbrev hop (F : Fritz E B R)(i j : Place E B) := halve R* F.rose i j
omit [Fintype E][Fintype B] in
lemma hopGrade : Graded ø false F.hop:=by rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first|rfl| (simp [hop,rose] at h)
omit [Fintype E][Fintype B] [Algebra ℚ R] in
lemma blankets (i j : Place E B) : F.rose i j=sting (ø i && ø j) (F.rose j i):=by
  rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> first| exact F.symm ..| (simp [rose,ø])
abbrev signClose (K : Place E B→Place E B→R)(S:Floor E B R) := touch K Finset.univ S []
lemma tap (i j : Place E B): signClose F.hop (varC R ø i*varC R ø j)= F.rose i j:=by
  unfold signClose; rw [touch_pair (Finset.mem_univ _) (Finset.mem_univ _)]; unfold hop; rw [← mul_sting, ← F.blankets i j,← add_mul,halve_twice,one_mul]
-- polarization of P*q. Count all orientations of Eta permitted operator. Need measures?
def handle : Strip E B R:=⟨r • (P.X * F.U.transpose+F.H*P.Z.transpose), r • (F.U.transpose*P.X)⟩

-- trick define vector q symbols generic matrix form on Generator i. Then polynomial identities only test entries. Foot evaluation not normalized.
def line (i j : Place E B) : R:= match i,j with
 | .inl (.inl i),.inr (.inl j)=> r*P.X i j
 | .inl (.inr i),.inl (.inl j) => r* P.Z i j
 | .inr (.inr i),.inl (.inr j) => r*P.X j i
 | _,_=>0
lemma kick (i:Place E B): P.q r (varC R ø i)=∑ j:Place E B,line P r i j • varC R ø j:=by
  rcases i with (i|i)|(i|i)
  · rw [show varC R ø (Sum.inl (Sum.inl i))=(A R i:Floor E B R) from rfl,P.qA r i]
    simp only [Finset.smul_sum,Fintype.sum_sum_type,line,zero_smul,Finset.sum_const_zero, add_zero, zero_add,smul_smul]
  · rw [show varC R ø (Sum.inl (Sum.inr i))=(K R i: Floor E B R) from rfl,P.qK r i]
    simp only [Finset.smul_sum,Fintype.sum_sum_type,line,zero_smul,Finset.sum_const_zero, add_zero,smul_smul]
  · rw [show varC R ø (Sum.inr (Sum.inl i))=(C R i: Floor E B R) from rfl,P.qC r i]; simp [line]
  rw [show varC R ø (Sum.inr (Sum.inr i))=(L R i:Floor E B R) from rfl,P.qL r i]; simp only [Finset.smul_sum,Fintype.sum_sum_type,line, zero_smul,Finset.sum_const_zero,zero_add,add_zero,smul_smul]
lemma shift (i j : Place E B) :
 signClose F.hop (P.q r (varC R ø i*varC R ø j))=(∑ x:Place E B,line P r i x * F.rose x j)+(∑ x:Place E B,line P r j x * sting (ø i) (F.rose i x)):=by -- also second sign of deriv true
  have ht (x y : Floor E B R): P.q r (x*y)=P.q r x * y+plane true x*P.q r y:= cross_leib P.tone (Strip.work _)
  unfold signClose; rw [ht, kick P r i,kick P r j,(var_tone (ρ:=ø) (R:=R) i).pl,map_add,plus_read, Finset.sum_mul, Finset.mul_sum,map_sum,map_sum,sum_read,sum_read];
  simp_rw [smul_mul_assoc,mul_smul_comm,map_smul, smul_read]; refine congr_arg₂ _ ?_ (Finset.sum_congr rfl fun x _=>?_);
  · exact Finset.sum_congr rfl fun _ _=> congr_arg _ (F.tap ..)
  cases ø i <;> simp [show touch F.hop Finset.univ _ []= F.rose i x from F.tap ..]
private lemma AK (i:E)(j:E): signClose F.hop (P.q r (A R i*K R j))= signClose (F.handle P r).footing (A R i*K R j):=by
  unfold A K; rw [F.shift, signClose,touch_pair (Finset.mem_univ _) (Finset.mem_univ _)];
  simp only [Fintype.sum_sum_type,line,rose,ø,Place.a,Place.k,Strip.footing,Fritz.handle,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,mul_zero, add_zero,zero_add,Finset.sum_const_zero,Sum.elim_inl,sting_zero,sting_false,_root_.mul_add,Finset.mul_sum,_root_.mul_assoc]; congr 1; refine Finset.sum_congr rfl fun x _=>?_ ; ring
private lemma CL (i j:B): signClose F.hop (P.q r (C R i* L R j))=signClose (F.handle P r).footing (C R i* L R j):=by
  unfold C L; rw [F.shift,signClose,touch_pair (Finset.mem_univ _) (Finset.mem_univ _)]; simp only [Fintype.sum_sum_type,line,rose,ø,Place.l,Place.c,Strip.footing,Fritz.handle,Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul,mul_zero, add_zero,zero_add,Finset.sum_const_zero,Sum.elim_inl, Sum.elim_inr,sting_zero,sting_true,mul_neg,Finset.mul_sum , neg_zero,← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _=>by ring
lemma close (i j:Place E B): signClose F.hop (P.q r (varC R ø i*varC R ø j))=signClose (F.handle P r).footing (varC R ø i*varC R ø j):=by
  have he (i j:Place E B): (signClose F.hop (P.q r (varC R ø i*varC R ø j)))=(signClose (F.handle P r).footing (varC R ø i*varC R ø j))→ signClose F.hop (P.q r (varC R ø j*varC R ø i))=signClose (F.handle P r).footing (varC R ø j*varC R ø i):=by
    intro ht; rw [(var_tone (ρ:=ø) j).commute (var_tone (ρ:=ø) i)]; unfold signClose at *; cases ø j<;>cases ø i<;> simp [ht]
  rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)
  case inl.inl.inl.inr=> exact F.AK .. -- maybe case labels chain flattened
  case inl.inr.inl.inl=> exact he _ _ (F.AK ..)
  case inr.inl.inr.inr=> exact F.CL ..
  case inr.inr.inr.inl=> exact he _ _ (F.CL ..)
  all_goals (rw [shift,signClose, touch_pair (Finset.mem_univ _) (Finset.mem_univ _)]; simp only [Fintype.sum_sum_type,line,rose, Strip.footing,Finset.sum_const_zero,mul_zero,zero_mul,sting_zero,add_zero])

lemma lodges : reflects (P.q r) (-(touch (F.handle P r).footing Finset.univ)) F.hop Finset.univ:=by
  -- detector Touch. Matrix test discharged already.
  refine corresponds (Rotor.tethered (Strip.work r) (P.rank.cap _ _)) F.hopGrade ?_ (fun i hi j hj=> ?_); · rw [← zero_sub]; exact (Twin.none.sub (Twin.is _ _ _))
  dsimp only; rw [show touch F.hop Finset.univ (varC R ø i*varC R ø j)=_ from (Twin.is ..).vacate, show P.q r (put ø _)=0 from cross_put_right _ (Strip.work r)] -- choose i etc
  rw [show touch F.hop Finset.univ _ []= _ from F.close P r i j]; change (0:R)=_+ -_; exact (add_neg_cancel _).symm
end Fritz
end YM.MSBar.Cutis
