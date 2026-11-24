import YM.AlbaMS.Cutis.Tonic

/-!
# Wires at finite slots individually in color sectors. Powers/effectiveories

Allow change in K separate from A. `composed` used with Landau projections.
Bootstrap mean vs based not requiring derivative at tip. Keep matrices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter IsNilpotent LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Coil Loft Inlay Inlay.Net Odom Lattice Nexus
variable {X E B V W R S : Type*} [Fintype E][Fintype B][Fintype V][Fintype W][CommRing R][CommRing S]
@[ext] structure Wire (E B V W R : Type*) where
 a : Matrix E V R
 k : Matrix E V R
 c : Matrix B W R
 l : Matrix B W R
namespace Wire
variable (P:Wire E B V W R){I J : Type*}(F:Fritz V W R)
def fee : Place E B→ Place V W→ R
| .inl (.inl i),.inl (.inl j)=> P.a i j
| .inl (.inr i),.inl (.inr j)=> P.k i j
| .inr (.inl i),.inr (.inl j)=> P.c i j
| .inr (.inr i),.inr (.inr j)=> P.l i j
| _,_=>0
omit [Fintype E][Fintype B][Fintype V][Fintype W] in
lemma stub : Routes ø ø P.fee:=by rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h <;> first| rfl|exact False.elim (h rfl)
def firm : Floor E B R→ₗ[R] Floor V W R:=shot Finset.univ P.fee P.stub
omit [Fintype V][Fintype W] in
lemma firm_mul (U Z : Floor E B R): P.firm (U*Z)=P.firm U * P.firm Z:= shot_mul ..
omit [Fintype V][Fintype W] in
def atlas (A:R→+* S) : Wire E B V W S:=⟨P.a.map A,P.k.map A,P.c.map A,P.l.map A⟩
def compose (L: Wire V W I J R) : Wire E B I J R:=⟨P.a * L.a,P.k* L.k,P.c* L.c,P.l *L.l⟩
omit [Fintype E][Fintype B] in
lemma line_f (L:Wire V W I J R)(i j) : (P.compose L).fee i j=∑ x:Place V W, P.fee i x* L.fee x j:=by
  rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> simp only [compose,fee,Fintype.sum_sum_type,mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero,Matrix.mul_apply]
lemma sketch (L:Wire V W I J R)(U:Floor E B R): L.firm (P.firm U)=(P.compose L).firm U:=accumulate (fun i _ j=>line_f P L i j)
def crib (a:Fritz V W R): Fritz E B R where
 H := P.a*a.H*P.aᵀ
 U := P.k*a.U*P.cᵀ
 symm i j:= by
   let Q:=P.a*a.H*P.aᵀ; have he:Qᵀ=Q:=by unfold Q; rw [transpose_mul, transpose_mul,transpose_transpose, a.H_t, Matrix.mul_assoc]
   exact congr_fun (congr_fun he j) i
omit [Fintype E][Fintype B][Fintype V][Fintype W] in
lemma linked (A:R→+* S)(i j): (P.atlas A).fee i j=A (P.fee i j):=by rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> first|rfl|(simp [fee])
omit [Fintype V][Fintype W] in
lemma visits (A:R→+* S)(U:Floor E B R): (P.atlas A).firm (Wind _ A U)=Wind _ A (P.firm U):=by
  unfold firm; have he : ∀ i,(P.atlas A).fee i=fun j=> A (P.fee i j):=fun i=> funext (P.linked A i)
  symm; have hv:=funext he; rw [shot_wind (H:=P.stub) A (hv ▸ (P.atlas A).stub)]; congr; exact hv.symm

omit [Fintype E][Fintype B] in
lemma plays (A:R→+* S): (P.crib F).replic A = (P.atlas A).crib (F.replic A):=by
  unfold crib atlas Fritz.replic; congr 1 <;> simp only [Matrix.map_mul, transpose_map]

variable [Algebra ℚ R]
-- matrix evaluation triple
omit [Fintype E][Fintype B] [Algebra ℚ R] in
private lemma rank_se {L I Z : Type*}[Fintype I][Fintype Z](A: Matrix E I R)(H:Matrix I Z R) (B:Matrix L Z R)(i j) : (A*H*Bᵀ) i j=∑ k:I,∑ z:Z,A i k*H k z*B j z:=by rw [Matrix.mul_apply]; simp_rw [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]; rw [Finset.sum_comm]
omit [Fintype E][Fintype B] in
lemma issue (i j:Place E B): (P.crib F).hop i j=∑ a:Place V W,∑ b:Place V W,P.fee i a*F.hop a b*P.fee j b:=by
  have he (x y z:R): x*(halve R*y)*z=halve R *(x*y*z):=by ring
  have hp (x y z:R): x*(halve R* -y)*z= -(halve R *(x*y*z)):=by ring
  -- Submatrices. check C blocks after previous.
  rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;>
    simp only [Fintype.sum_sum_type,fee,crib,Fritz.hop,Fritz.rose,mul_zero,zero_mul, Finset.sum_const_zero,add_zero,zero_add]
  · rw [rank_se]; simp_rw [Finset.mul_sum, ← he]
  · rw [rank_se]; simp_rw [mul_neg,Finset.mul_sum, ← Finset.sum_neg_distrib,neg_mul, ← he]
  rw [rank_se P.k]; rw [Finset.sum_comm (s:=(Finset.univ:Finset W))]; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun y _=>?_ ; ring

lemma draws (A : Floor E B R)(h:FinRank A): Fritz.eval (P.crib F).hop A= Fritz.eval F.hop (P.firm A):=by
  unfold Fritz.eval firm; rw [shot_wither _ (fun i _ j _=> P.issue F i j) h]; rfl -- guess param order
end Wire
end YM.MSBar.Cutis
