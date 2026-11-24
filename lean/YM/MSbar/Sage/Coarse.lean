import YM.MSbar.Sage.Temper
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V' :Config G n}{x:Site n}{R:PathData G}{σ C T a v δ w β:ℝ}
open Finset RG.PathData
variable {Y X: Support n}{k M:ℕ}{p:BudgetPoint}{d:Clip}
open AnalyticBridge.VerifiedReset Next.Scheduling Precision
variable (A:ℕ→Atom G k)(hp:Place Y M U U' V V' p.threshold)
lemma unmasked_summ (he :0<σ)(hh: SumBudget (fun i=>(A i).budget σ) C) (j:Site n) (U:Config G n) : Summable (fun i=>(A i).unmasked U j) := by
    exact (hh.2.1.mul_right (2^k)).of_norm_bounded (fun i=> ((A i).unmasked_bound U j).trans (mul_le_mul_of_nonneg_right (Atom.lower_budget (A i) σ he) (by positivity)))
include hp
lemma gassed (he:0<σ)(hh : SumBudget (fun i=> (A i).budget σ) C) : |((∑ x:Site n, atomSeries A p U x)- uncut A U')-((∑ x:Site n, atomSeries A p V x) - uncut A V')| ≤ C*crownAtom σ k*cape Y.card σ M:=by
   let f i j:= A i|>.placed p U j; let g i j:= A i|>.placed p V j; let t:=crownAtom σ k; have ht:0≤ t:=by unfold t crownAtom; positivity
   have hz :0≤ C:= budget_nonneg hh
   have ha (x:Site n)(U V:Config G n) : HasSum (fun i=>addOn (A i) p U V x) (atomSeries A p U x - ∑' i,(A i).unmasked V x) := ((PathData.atom_dominated A p x he hh|>.summable U).hasSum.sub (unmasked_summ A he hh _ _|>.hasSum)) -- defEq
   let I(i:Site n):= silk M σ Y i; have hH(i:Site n): |(atomSeries A p U i-∑' j,(A j).unmasked U' i)-(atomSeries A p V i -∑' j,(A j).unmasked V' i)| ≤ C*t*I i:=by
       rw [← (ha i U U').tsum_eq, ← (ha i V V').tsum_eq]; apply cherished _ _ _ (ha _ _ _).summable (ha _ _ _).summable ?_ (fun j=> atom_mismatch (A j) hp he) -- order
       have hx:C*t*I i=(I i*t)*C:=by ring
       rw [hx]; convert budget_scale (mul_nonneg (silk_pos M σ Y i) ht) hh using 1; ext; unfold t; ring -- possible I
   unfold uncut; rw [←sum_sub_distrib,←sum_sub_distrib,←sum_sub_distrib]; refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _=> hH i)).trans ?_); rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (silk_pays _ he Y) (mul_nonneg hz ht)
variable (h:R.Bounds d σ C T) (hk:p.B≤M)(hd:Decent d p) (hβ:0≤ β)
def craft (C σ β:ℝ)(y M:ℕ):= β*(16*C^2*Fintype.card PlaqAxes + C*(crownAtom σ 3+crownAtom σ 4))*cape y σ M
include h hk hd hβ
open Bid
local notation "core"=> R.principal d p β
-- precision loop unmasked with halo compare.Need cost difference to actual tested uses Δ ̂: show ≤T * t²* Y.
def regularP (U : Config G n) (B : PathData G) (d:Clip) :=quadratic d B U+ Precision.uncut B.cubic U+ Precision.uncut B.quartic U
lemma bud : |((core U)- ∑ j : Site n, atomSeries R.loop p U j) - ((core V)- ∑ j:Site n, atomSeries R.loop p V j)-β*(regularP U' R d-regularP V' R d)| ≤ craft C σ β Y.card M:=by
    let f(U:Config G n):=∑ x,R.baseTerm d p U x; have he(W X:Config G n): f W - quadratic d R X=∑ i,bCost R p d W X i:=by unfold f quadratic bCost; rw [←sum_sub_distrib]
    have hf(x):= soreness h x hp hk hd
    let g:=cape Y.card σ M
    have h₁ : |(f U-quadratic d R U')-(f V-quadratic d R V')| ≤ (16*C^2* Fintype.card PlaqAxes)*g:=by
       rw [he,he,←sum_sub_distrib]; apply le_trans (Finset.abs_sum_le_sum_abs ..) ((sum_le_sum (fun x _=> hf x)).trans ?_)
       change ∑ i: Site n × PlaqAxes,_ ≤ _; rw [Fintype.sum_prod_type, Finset.sum_comm]; dsimp only; rw [Finset.sum_const]
       rw [card_univ,nsmul_eq_mul, ← mul_sum,← mul_assoc, mul_comm _ (16*C^2)]; exact mul_le_mul_of_nonneg_left (silk_pays _ h.width Y) (by positivity)
    have h₂:= gassed R.cubic hp h.width h.three; have h₃:= gassed R.quartic hp h.width h.four; let J(k:ℕ)(W :ℕ→Atom G k)(U : Config G n):= ∑ i, atomSeries W p U i
    let q(W V:Config G n):=(f W-quadratic d R V)+(J _ R.cubic W-uncut R.cubic V)+(J _ R.quartic W-uncut R.quartic V)
    have hP(z l s t : Config G n): (core z)- ∑ j:Site n, atomSeries R.loop p z j - ((core s)- ∑ j:Site n, atomSeries R.loop p s j)-β*(regularP l R d-regularP t R d)=β*(q z l-q s t):=by unfold PathData.principal q regularP f J; simp_rw [sum_add_distrib]; ring
    rw [hP,abs_mul,abs_of_nonneg hβ]; unfold q; rw [add_sub_add_comm,add_sub_add_comm _ (J _ _ _ - _) (f V- _) _] -- keep manual
    refine (mul_le_mul_of_nonneg_left ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add h₁ h₂)) h₃)) hβ).trans_eq ?_
    unfold craft g; ring
end YM.MSbar.Heath
