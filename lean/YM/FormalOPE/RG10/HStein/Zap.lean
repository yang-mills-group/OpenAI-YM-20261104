import YM.FormalOPE.RG10.Routes.Episode
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Stein
import Mathlib.Algebra.MvPolynomial.PDeriv -- inspect
/-!
# Stein--polynomial method for bounding repeated formal transmissions in Route's Episode

 Later uses exact dictionary from WilsonX normalized step. Here no supp/change-of-scale
 estimates. Germ $ℂ[p]⟦β⟧$ at any joint arity for relative coarse fields.
 Need *still* structural width/rank/kernel etc hypotheses on the Fk UV cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.HStein
open PowerSeries Function MeasureTheory Metric Filter Topology
open Route Route.Bulk Multi.Vacuum.Gauss Primitives.GCC
open scoped Topology BigOperators ContDiff Classical
variable {B I J : Type} [Fintype J] [Fintype I]
local notation "W"=> Packet (I⊕B)
variable (q : I→Row J)(p r : Packet (I⊕B))(b:B→ℂ)(x:Row J)(a:I)

def score (z w : I): ℂ := ↑(crossed (q z) (q w))
def uptick (i:I) : Derivation ℂ (Packet (I⊕B)) (Packet (I⊕B)) := ∑ j, score q j i • MvPolynomial.pderiv (Sum.inl j)
def evaluate (u:Row J): Packet (I⊕B) →ₐ[ℂ] ℂ:= MvPolynomial.aeval (Sum.elim (alongFine q u) b)
local notation "T"=> study q b

omit [Fintype I] in
private lemma devSum (s:Finset I) (f:I→ Derivation ℂ W W): (∑ i∈s,f i) p=∑ i∈s,f i p:=by
  induction s using Finset.induction_on with
  | empty=> simp
  | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Derivation.add_apply,ih]
lemma deriva : uptick q a p=∑ i, score q i a • (MvPolynomial.pderiv (Sum.inl i) p):= by unfold uptick; rw [devSum]; rfl
lemma tick_axis (i:I⊕B): uptick q a (MvPolynomial.X i)= match i with
 | .inl v=> MvPolynomial.C (score q v a)
 | .inr _ => 0 := by
 unfold uptick; cases i with
 | inr i=> simp_rw [devSum]; simp [MvPolynomial.pderiv_X] -- Finsum?
 | inl i=>
   change (∑ j, score q j a • MvPolynomial.pderiv (Sum.inl j)) (MvPolynomial.X (.inl i))= _; simp_rw [devSum];
   rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)];
   · rw [Derivation.smul_apply, MvPolynomial.pderiv_X_self]; exact (Algebra.algebraMap_eq_smul_one (score q i a)).symm
   intro v _ hv; rw [Derivation.smul_apply,MvPolynomial.pderiv_X]; simp [hv]

lemma news : Differentiable ℝ (fun u=> evaluate q b u p) ∧ ∀ x:Row J,
   fderiv ℝ (fun u=> evaluate q b u p) x (q a)=evaluate q b x (uptick q a p) := by
 let D p:= uptick q a (B:=B) p; induction p using MvPolynomial.induction_on with
 | C c => simp_rw [evaluate,MvPolynomial.aeval_C]; exact ⟨differentiable_const _,fun x=>by rw [show uptick q a (MvPolynomial.C (σ:=I⊕B) c)=_ from Derivation.map_algebraMap (uptick q a) c]; simp⟩ -- name
 | add p r hp hr=> simp_rw [map_add]; exact ⟨hp.1.add hr.1,fun x=> by rw [fderiv_fun_add (hp.1 x) (hr.1 x),_root_.add_apply,hp.2,hr.2]⟩
 | mul_X p i hp=>
   let G(u:Row J):= evaluate q b u (MvPolynomial.X i); let G'(u:Row J):= evaluate q b u (uptick q a (MvPolynomial.X i))
   have hg: Differentiable ℝ G ∧ ∀ x:Row J,fderiv ℝ G x (q a)=G' x:= by
      cases i with
      | inl i=>
        unfold G G' evaluate; simp_rw [tick_axis,MvPolynomial.aeval_X,MvPolynomial.aeval_C, Sum.elim_inl]; unfold alongFine
        exact ⟨Complex.ofRealCLM.differentiable.comp (fun x=>(crossed_deriv (q i) x).differentiableAt),fun x=>by change fderiv ℝ (Complex.ofRealCLM ∘ crossed (q i)) x _= _; rw [(Complex.ofRealCLM.hasFDerivAt.comp x (crossed_deriv (q i) x)).fderiv,ContinuousLinearMap.comp_apply,plane_read]; rfl⟩
      | inr i=> unfold G G' evaluate; simp_rw [tick_axis,MvPolynomial.aeval_X,Sum.elim_inr, map_zero]; exact ⟨differentiable_const _,fun x=>by simp⟩
   simp_rw [Derivation.leibniz,_root_.map_mul,map_add]; -- smul issue W instance.R
   constructor
   · exact hp.1.mul hg.1
   intro x; rw [fderiv_fun_mul (hp.1 x) (hg.1 x),_root_.add_apply,_root_.smul_apply,_root_.smul_apply,hp.2,hg.2]; simp_rw [smul_eq_mul, map_mul]; rfl

omit [Fintype I] in
lemma financed : Integrable (fun x=> evaluate q b x p) (standard J):= by
 have he := Joins.Gauss.accepted J (study q b p).val (study q b p).property ()
 simp_rw [Route.study_apply] at he; simpa [Joins.Gauss.standardFeed,evaluate] using he -- phi unfold?
omit [Fintype I] in
lemma average (i:B):evaluate q b x (MvPolynomial.X (Sum.inr i))=b i:= by simp [evaluate]
omit [Fintype I] in
lemma lobby : Bulk.mean (study q b p) = ∫ x,evaluate q b x p ∂ standard J:= by
 change (Joins.Gauss.standardFeed J).mean (study q b p).val = _; unfold FlatFeed.mean; simp_rw [Route.study_apply]; simp [Joins.Gauss.standardFeed,evaluate]
lemma steam : hand q (MvPolynomial.X (.inl a) * p)= hand q (uptick q a p):= by
 apply Route.all_conf; intro b; rw [Bulk.hand_eq,Bulk.hand_eq,lobby,lobby];
 have hx:∀ x:Row J,evaluate q b x (MvPolynomial.X (.inl a):Packet (I⊕B))=(↑(crossed (q a) x):ℂ):=by simp [evaluate,alongFine];
 let f x:= evaluate q b x p; have he:= news q p b a -- order
 have hp x:evaluate q b x (MvPolynomial.X (.inl a) * p)=crossed (q a) x • f x:= by rw [map_mul,hx,Complex.real_smul]
 have hy : Integrable (fun x=>crossed (q a) x • f x) (standard J):= by
   have H := financed (q:=q) (p:=(MvPolynomial.X (.inl a)*p)) b -- partial application? type infer buried
   rw [funext hp] at H
   exact H
 have hz : Integrable (fun x=>fderiv ℝ f x (q a)) (standard J):= by unfold f; simp_rw [he.2]; exact financed q _ b
 simp_rw [hp,← he.2]; exact weighted_stein (q a) f he.1 (financed q p b) hy hz
end YM.FormalOPE.RG10.HStein
