import YM.AlbaMS.Cutis.Signals
/-!
# Kill the elementary shift charge, using color-blind projection

Full Position Gram not diagonal when curvature loop, but initial horizon
means use root A,K independent orth bases. Also record bridges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Cutis
open Set Function Filter LinearMap Matrix
open scoped BigOperators Classical Topology Matrix InnerProductSpace ENNReal
open Bric Coil Loft Inlay Inlay.Net Odom Lattice Nexus
variable {E B V W R S : Type*}[Fintype E][Fintype B][Fintype V][Fintype W][CommRing R][CommRing S]
namespace Wire
variable (P:Wire E B V W R)
lemma acts (i:Place E B): P.firm (varC R ø i)=∑ j:Place V W,P.fee i j • varC R ø j:=by
  unfold firm; apply deep; rw [shot_nil,sum_read]; simp
  intro j; rw [map_sum,shot_D,drip_apply, Finset.sum_eq_single i]; rw [map_smul,varD,if_pos rfl,Finset.sum_eq_single j]; rw [map_smul, varD, if_pos rfl, show shot Finset.univ _ P.stub 1=1 from shot_put _ _ 1] -- fix shot_put 1
  all_goals first|(intro x _ hx;simp [hx,Ne.symm hx])|simp
lemma actK (i:E) : P.firm (K R i)=∑ j:V,P.k i j • K R j:=by unfold K; rw [acts]; simp only [Fintype.sum_sum_type,Place.k,Wire.fee, zero_smul, Finset.sum_const_zero,zero_add,add_zero]
lemma actA (i:E) : P.firm (A R i)=∑ j:V,P.a i j • A R j:=by unfold A; rw [acts]; simp only [Fintype.sum_sum_type,Place.a,Wire.fee, zero_smul, Finset.sum_const_zero,add_zero]
lemma actL (i:B) : P.firm (L R i)=∑ j:W,P.l i j • L R j:=by unfold L; rw [acts]; simp only [Fintype.sum_sum_type,Place.l,Wire.fee, zero_smul, Finset.sum_const_zero,zero_add]

-- block sum bridge for a simple charge. Uses matrices lift for later E.
lemma block (Q: Matrix E E R): P.firm (∑ i:E,K R i * ∑ j:E,Q i j • A R j) = ∑ i:V,∑ j:V,(P.kᵀ * Q * P.a) i j • (K R i*A R j):=by
  simp_rw [map_sum,P.firm_mul,map_sum,map_smul, P.actK,P.actA, Finset.mul_sum, Finset.smul_sum, Finset.sum_mul]; -- arrange ordering
  simp_rw [Finset.mul_sum,smul_mul_assoc, mul_smul_comm,smul_smul, Matrix.mul_apply, Finset.sum_mul]; simp_rw [Finset.sum_comm (s:=(Finset.univ:Finset E)) (t:=(Finset.univ:Finset V))]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; simp_rw [Finset.sum_smul,Matrix.transpose_apply]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>?_ ; rw [_root_.mul_assoc]
  -- try by promoting outer K lifted and inner A. expr. expected
end Wire

namespace Winter
-- turn c matrix uses G Lie normalization.
variable {G:Gauge}[DecidableEq E][DecidableEq V]
-- lemma gram
abbrev dash (E:Type*) (c:G.Color):= Matrix.of (turn (V:=E) c)
omit [Fintype E] in
lemma TurnP (i j:E)(a b:G.ColorIndex)(c:G.Color): turn c (i,a) (j,b)=if i=j then coefQ a (G.ad c (base G b)) else 0:=by unfold turn stip; change coefQ a (G.ad c (slabQ (j,b) i))=_; rw [Inlay.slab]; by_cases he:i=j<;> simp [he]
lemma share (P:Matrix E V ℝ)(c:G.Color): dash E c * dotC G P=dotC G P* dash V c:=by
  ext ⟨i,a⟩ ⟨j,b⟩; simp only [Matrix.mul_apply, Fintype.sum_prod_type,dash,dotC,TurnP,chip,Matrix.of_apply,ite_mul, mul_ite, MulZeroClass.mul_zero,MulZeroClass.zero_mul]; -- promote bow
  simp [mul_comm]
end Winter
end YM.MSBar.Cutis
