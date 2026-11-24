import YM.AllOrder.Rosary.Foil
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
namespace Guard
open Next.Scheduling Finset
-- cent one label per true anchor keep orient & cost. Used for identification β projection on unbounded sizes.
def hilt (i:Site n):RegularAddress n:=⟨i,halo 2 {i},halo_subset _ _ (mem_singleton_self _)⟩
variable (u:ℝ)(p)
def ruby (n:Side)(G:Gauge)(u:ℝ): Herb G n (Site n):=⟨hilt,fun i=> u • counter Lapis.kappa i⟩
def priceR (G:Gauge)(p:BudgetPoint)(u:ℝ) :ℝ:=|u| * ((2:ℝ)⁻¹*∑ x:PlaqAxes, ∑ y:PlaqAxes, |Lapis.kappa x y| * (pairBill G p*p.threshold^2))
def costR (G:Gauge)(p:BudgetPoint)(u:ℝ):ℝ:=priceR G p u*Real.exp ((preExponent p)*81)
variable {p}
local notation "X"=> ruby n G u
lemma tiny_rows {κ':ℕ}(t:Herb G n (Site n))(ha:∀ i,(t.addr i).site=i) (hv:∀ i,coverNumber p.B (t.addr i|>.support)≤(κ':ℕ)) (hz:t.spins) (hh:∀ i,p.Regular (t.addr i).support (t.values i)∧ p.supBounds i (t.addr i).support (t.values i) C): t.Proto p (C*Real.exp (preExponent p*κ')):=by
 refine ⟨hz, fun _=> C,fun i=> ha i|>.symm ▸ hh i,?_⟩; intro x; simp only [ha]; have hz:= hh x|>.2.1; refine ⟨fun i=>?_,Summable.of_finite,?_⟩
 · dsimp only; split; exact mul_nonneg hz (Real.exp_pos _).le; exact le_rfl
 rw [tsum_fintype]; simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
 refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hz; have hs : 0 ≤ preExponent p:= (by unfold preExponent; linarith [p.exponent_pos]); exact mul_le_mul_of_nonneg_left (by exact_mod_cast hv x) hs
lemma greet(i:Site n) (U:Config G n) : ((X).values i U)= u*((∑ k,‖petals U i k‖^2)/2):=by change u*counter Lapis.kappa i U=_; simp only [counter,VerifiedReset.quad,Lapis.kappa,ite_mul,one_mul,zero_mul]; simp
lemma carry (t:Signed)(b:Site n)(i:Site n): (X).values (affine t b i)=(X).values i ∘ pull t b:=by
 ext1 U; rw [greet]; simp_rw [Function.comp_apply, greet,petals_moves,reframe_norm]; rw [Equiv.sum_comp (PlaqAxes.transform t) (fun k=>‖petals U (affine t b i) k‖^2)] -- arg
variable (g:G.Simple)(hc:2≤p.B)(hn:20<n.val)
include hc hn g
local notation "a"=> axes01
lemma marveled : (X).Proto p (costR G p u)∧ (X).mu=u:=by
 have he i: Nonwrapping (expand ((X).addr i)) i :=by
    intro j hj; rw [show expand _=halo 2 {i} from (by change halo 2 {i} ∪ halo 2 {i}=halo 2 {i}; simp)] at hj; obtain ⟨y,hh,ht⟩:= halo_spec.mp hj; rw [mem_singleton.mp hh,separation_comm] at ht; omega
 constructor
 · refine tiny_rows (ruby n G u) (p:=p) (κ':=81) (fun i=> rfl) (fun i=>?_) (fun s b=> ⟨Push.Local.turnSites s b,fun i=> ⟨rfl,?_,carry u s b i⟩⟩) ?_
   · exact (Corona.cover_mono (Corona.halo_mono hc (Finset.Subset.refl ({i}:Support n))) p.B).trans (tiles p i)
   · let e:= Push.Local.turnSites s b; change halo 2 {e i}= _; rw [← Finset.image_singleton]; exact Push.Local.halo_map e (Push.Local.turn_sep s b) ..
   intro i; exact ⟨CouplingShape.reg_scale _ (counter_regular i _ _), CouplingShape.sup_scale u (Bill.sup (counter_bill i Lapis.kappa p) (fun U hh=> healthy_mono (halo_subset 2 _) hh))⟩
 unfold Herb.mu; rw [tsum_fintype]; let ξ:=wedge a (spike G); let o:Site n:=0; rw [sum_eq_single o]
 · have hx:= counter_diag g p o hn ξ Lapis.kappa; let f:=counter Lapis.kappa o (G:=G); have hr: ContDiffAt ℝ 2 (f ∘ increment (1:Config G n)) 0:= germ_diff (counter_regular o _ p); rw [Herb.shofar,if_pos (show ((X).addr o).site= 0 from rfl),projection,show ((X).addr o).site=o from rfl,if_pos (he o)]; change iteratedFDeriv ℝ 2 (u • (f ∘ increment 1)) 0 _=u; rw [iteratedFDeriv_const_smul_apply («a»:=u) hr]; change u*(logHessian f (ξ.field 0) (ξ.field 0))= _; rw [show logHessian f _ _ = _ from hx]; unfold ξ VerifiedReset.quad; simp_rw [curl_wedge]; -- simp
   simp [Lapis.kappa,ite_mul]; rw [Finset.sum_eq_single (a)]; simp [spike_norm g]; intro i hi ih; simp only [if_neg ih.symm]; simp; simp
 · intro i hi he; exact if_neg he
 simp
lemma gems (U:Config G n)(hw:flags p.threshold U=∅): (X).teller p U=u*∑ i,heads p i U:= by
 have ht (x:Support n): Healthy p.threshold x U:= by unfold Healthy; rw [hw]; simp
 rw [Herb.teller,tsum_fintype, mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Herb.occG heads; rw [masked_eq _ _ _ _ (ht _),masked_eq _ _ _ _ (ht _),greet]
end Guard
end YM.AllOrder.Rosary
