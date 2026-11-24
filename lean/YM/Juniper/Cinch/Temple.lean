import YM.Juniper.Cinch.Lift
set_option autoImplicit false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
local notation "p"=> Averaging.axes01
open Quotes Finset Matrix Further.LogJets Pert.Kinetic Pressure
set_option quotPrecheck false
variable {U V':Listing G c}{A B:Collection.Source G c}{b d v w τ σ : ℝ}(h : Collection.Local U W A b v)
  (hB: Collection.Local V' W B d w)(hG:G.Simple)
local notation "N"=> (Fintype.card (Site c):ℝ)
local notation "V"=> Directions G c
local notation "Ω"=> W.supportExponent
-- use EXACT minimal. first/period aran.
lemma ceremonial {f : ℕ → ℝ} (he : early W U.reg f b): SumBudget (fun i=> f i* Real.exp (preExponent W * coverNumber W.B (U.reg i).support)) (N*b):= by
    have hv := budget_over univ _ (fun _=>b) (fun x (_:x∈ (univ:Finset (Site c)))=> he x)
    simpa only [sum_const, Finset.card_univ, nsmul_eq_mul, sum_ite_eq, mem_univ,if_true] using! hv

def fare (P: BudgetPoint)(c:Side) := ((Fintype.card (Site c):ℝ)^2*(c.val:ℝ)^2)* (3/P.threshold^2)
lemma fare_pos (P: BudgetPoint)(c:Side): 0<fare P c:=by unfold fare; have he:=P.threshold_pos; positivity
lemma coordLo (x y:Site c) : coord x y (p).val.1 ^ 2 ≤ (c.val:ℝ)^2:= by
    rw [← sq_abs]; apply pow_le_pow_left₀ (abs_nonneg _); apply (small_coord x y _).trans; exact_mod_cast (show separation y x≤ c.val from (by unfold separation pdist; refine Finset.sup_le (fun i hi=>?_); have h:=lift_centers (y-x) i; omega))
include hG
lemma fine (x:Site c)(i:Edge (Site c)): ‖spot G x i‖ ≤1:=by
  by_cases he:(x,(p).val.2)=i; rw [← he]; simp [spot,spike_norm hG]; · simp [spot,he] -- lint
lemma chose {a:RegularAddress c} {f:Pot G c}(h:W.Regular a.support f)(he: W.supBounds a.site a.support f b): ‖coke f‖ ≤ fare W c*b:= by
   have hD (x y:Site c): ‖pullback (f:=f) x y‖≤ 3*b/W.threshold^2:= by
      let v(x:Site c)(e:Edge (Site c)):= spot G x e; have hp(x:Site c): W.dirBound a.site ((1/W.threshold)⁻¹ • spot G x) := Pert.Kinetic.loose_dir _ _ zero_lt_one 0 (Nat.zero_le _) (fun i=>by simp only [pow_zero,mul_one]; exact fine hG x i)
      exact (Pert.Kinetic.scaled_price hG h he _ _ zero_lt_one zero_lt_one (hp _) (hp _)).trans_eq (by ring)
   let f':= (c.val:ℝ)^2*(3*b/W.threshold^2)
   apply le_trans (norm_sum_le ..)
   suffices hh: ∀ i:Site c, ‖∑ j:Site c, coord i j (p).val.1^2*pullback (f:=f) i j‖ ≤ N*f' by apply le_trans (sum_le_sum (fun i _=> hh i)); rw [sum_const,card_univ,nsmul_eq_mul]; unfold fare f'; apply le_of_eq; ring
   intro i; apply le_trans (norm_sum_le ..); refine le_trans (sum_le_sum (g:=fun _=> f') (fun j _=>?_)) (le_of_eq (by simp)); rw [norm_mul,Real.norm_of_nonneg (sq_nonneg _)]; exact mul_le_mul (coordLo ..) (hD ..) (norm_nonneg _) (sq_nonneg _)

include h
abbrev turnFeeP (P:BudgetPoint) (c:Side):= fare P c * Real.exp (- ((preExponent P)* turnB P c))
local notation "f'"=> turnFeeP W c
def mint (i:ℕ):= coke (A.logRead i) +2*projection (U.reg i) (A.logRead i) p p
lemma dawn (hn:20<c.val) : |(∑' i,coke (A.logRead i))+2*(N*delta (U.read A))| ≤ f'*(N*b):= by
    let f:= mint (A:=A) (U:=U); obtain ⟨x,hx,hA⟩:= h.cheap
    let Z:=turnB W c; let r:= Real.exp (-(preExponent W*Z)); let u:=fare W c*r
    let g i:= x i* Real.exp (preExponent W*coverNumber W.B (U.reg i).support)
    have hp:SumBudget g (N*b):= ceremonial hA
    have he:0<u:= mul_pos (fare_pos ..) (Real.exp_pos _)
    have hX: 0≤preExponent W:= by unfold preExponent; linarith only [W.exponent_pos]
    have hh(i:ℕ) : ‖f i‖≤ u*g i:= by
       let a:=U.reg i; by_cases hz:Nonwrapping (expand a) a.site
       · unfold f mint; rw [tip hG (h.smooth i) (U.reg i) (by omega) rfl hz,neg_add_cancel,norm_zero]; exact mul_nonneg he.le (hp.1 i)
       have hf: projection a (A.logRead i) p p=0:= if_neg hz
       rw [show f i=coke (A.logRead i) from (by unfold f mint; rw [show projection _ _ _ _ = _ from hf,mul_zero,add_zero])]; apply le_trans (chose hG (h.smooth i) (hx i)); unfold u; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (fare_pos ..|>.le)
       have ht := (Nat.cast_le.mpr (turn_be W hn a hz) : ↑Z ≤ (coverNumber W.B a.support : ℝ)); have hu:1 ≤ Real.exp (preExponent W*((coverNumber W.B a.support:ℝ)-Z)):=Real.one_le_exp (mul_nonneg hX (by linarith)); unfold g r; rw [mul_comm (x i), ← mul_assoc, ← Real.exp_add]; rw [mul_sub] at hu; exact le_mul_of_one_le_left (hx i|>.1) (by rw [add_comm,← sub_eq_add_neg]; exact hu) -- add vs sub order adjust
    have hN:= budget_mono (budget_scale he.le hp) (fun i=> norm_nonneg _) hh
    have hζ: Summable (fun i=> coke (A.logRead i)):= summable_sum fun i _=> summable_sum fun j _=> (almond h hG (spot G i) (spot G j)|>.summable).mul_left _
    rw [shone h hG (by omega), ← tsum_mul_left, ← Summable.tsum_add hζ (show Summable fun i => 2*projection (U.reg i) (A.logRead i) p p from (h.projects.series hG p p).mul_left 2)]; exact (norm_tsum_le_tsum_norm (f:=f) hN.2.1).trans hN.2.2

include hB
lemma shimmer {K: PathData G} {c':Clip} {α β:ℝ} (hn:20<c.val)(he: earlyValue U K c' W A β τ α=earlyValue V' K c' W B β σ α) : |delta (U.read A)- delta (V'.read B)| ≤ (f') *((b+d)/2):= by
    have hM:=dawn h hG hn; rw [bloom h hB hG he] at hM; have hv:=dawn hB hG hn; have he: N>0:=by positivity
    suffices hh : (2*N)*|delta (U.read A)- delta (V'.read B)| ≤ turnFeeP W c*(N*(b+d)) by apply le_of_mul_le_mul_left (a:=2*N) _ (by positivity); nlinarith only [hh]
    let s:= ∑' i,coke (B.logRead i)
    let u:= s+2*(N*(delta (U.read A))); let v:= s+2*(N*(delta (V'.read B)))
    rw [show 2*N * |delta (U.read A)- delta (V'.read B)| = |u-v| from (by rw [← abs_of_pos (by positivity : 0<2*N),← abs_mul]; unfold u v; congr 1; ring)]
    exact (abs_sub _ _).trans ((add_le_add hM hv).trans_eq (by ring))
end YM.Juniper.Cinch
