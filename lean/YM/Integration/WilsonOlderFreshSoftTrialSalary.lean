import YM.Integration.WilsonOriginalPublicPivotSalary
import YM.Integration.WilsonOriginalPublicReflectedKWallet

/-! The independent soft comparison spends the measured input vector, including its constant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftTrialSalary
open Function Filter Finset Lattice Laurent Wilson RG Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout.Copper RG05Readout.Native RG05Readout.UV
open WilsonOriginalPublicTrialInput (vector)
open WilsonOriginalPublicTrialFigure (amount weight)
open WilsonOriginalPublicFigureIncome (height)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open WilsonCapturedPrimaryCoreBill (wrapFee)
open WilsonCoeffUV.Blue
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)

def wrap (k:ℕ):ℝ:=1+2*|wrapFee (R.family.labels.level k) R.family.params| *Real.exp 200

theorem wrapping (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d:ℕ):
    ∀ᶠ j:ℕ in atTop,(R.family.path.levels.budget j).supportExponent≤100 →
      1+wrapCost R d j≤wrap R d*(R.family.path.levels.clock.hatBeta j)^2:=by
  filter_upwards [WilsonThermometerOffsetLedger.original R simple shop d] with j invoice bound
  let L:=R.family.path.levels
  let H:=L.clock.hatBeta j
  have one:1≤H:=(L.fits.delayed j).le
  have h0:0<H:=zero_lt_one.trans_le one
  have gap:1+Real.log (2+Real.log H)≤2*H:=by
    have p:0<2+Real.log H:=by linarith [Real.log_nonneg one]
    linarith only [Real.log_le_sub_one_of_pos p,Real.log_le_sub_one_of_pos h0,one]
  have top:(L.params j).columns≤WilsonThermometerOffsetLedger.cash R d j:=by
    change (R.alloy.B.a.params j).columns≤_
    rw [Push.PriceCompiler.params_eq R.alloy.B.valid j]
    exact (cash_fill G d (R.alloy.B.a.clock.J j) R.metals.p.profile R.y).choose_spec.2.1
  have count:=top.trans (invoice.2.2.trans gap)
  let fee:=wrapFee (R.family.labels.level d) R.family.params
  have positive:0≤(L.params j).columns:=zero_le_one.trans (L.params j).columns_ge
  have bill:wrapCost R d j≤|fee| *Real.exp 200*(2*H):=by
    unfold wrapCost
    change fee * Real.exp (2*(L.budget j).supportExponent)*(L.params j).columns≤_
    apply mul_le_mul _ count positive (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    exact mul_le_mul (le_abs_self _) (Real.exp_le_exp.mpr (by linarith only [bound] ))
      (Real.exp_pos _).le (abs_nonneg _)
  have hp:0≤|fee| *Real.exp 200:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  change 1+wrapCost R d j≤(1+2*|fee| *Real.exp 200)*H^2
  have hh:1≤H^2:=one_le_pow₀ one
  have hH:H≤H^2:=by nlinarith only [sq_nonneg (H-1),one]
  nlinarith only [bill,hh,mul_le_mul_of_nonneg_left hH hp]

variable {ι:Type}[Fintype ι][LinearOrder ι]
theorem roster {α:Type}[Fintype α][LinearOrder α](d:α→ℕ)(g:ℝ)
    (z:∀i,(R.family.labels.level (d i)).Coeff)(M:α→ℝ)
    (each:∀i,(∑a,‖WilsonOriginalPublicTrialFigure.amount R d g z i a‖)≤M i):
    (∑b,‖WilsonOriginalPublicTrialFigure.weight R d g z b‖)≤∏i,M i:=by
  unfold WilsonOriginalPublicTrialFigure.weight
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i (a:(R.family.labels.level (d i)).Index)=>‖WilsonOriginalPublicTrialFigure.amount R d g z i a‖)]
  exact prod_le_prod (fun i _=>sum_nonneg fun _ _=>norm_nonneg _) fun i _=>each i

variable (d j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
  (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (d a))(before:∀a,j a≤K)
  (reg:WilsonOriginalMicroscopicGuardedPageSchool.Indexed R d j target η M Y)
local notation "F" i:max=>R.family.labels.level (d i)
local notation "H" i:max=>R.family.path.levels.clock.hatBeta (j i)
local notation "s" g:max=>Real.log (g:ℝ)⁻¹

def base (i:Fin 3):ℝ:=2^(height R (d i))*2*wrap R (d i)

theorem single (N per:ℕ)(live:K<N)(a:Fin 3)(g:ℝ)(g0:0<g)(g1:g≤1)
    (M0:0≤M a)(paper:1+wrapCost R (d a) (j a)≤wrap R (d a)*(H a)^2):
    (∑b,‖WilsonOriginalPublicTrialFigure.amount R d g
      (vector R d j K target η M Y before reg N per) a b‖)≤
    base R d a*(H a)^2*M a*
      Real.exp ((height R (d a):ℝ)*s g+η*Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹):=by
  apply (WilsonOriginalPublicPivotSalary.original R d j K target η M Y before reg (j a) N per live a g g0 g1).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [WilsonOriginalPublicPivotSalary.fixed,sub_self,mul_zero,Real.exp_zero,mul_one]
  calc
    _ ≤ 2^(height R (d a))*2*((wrap R (d a)*(H a)^2)*M a):=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right paper M0) (by positivity)
    _ = _:=by unfold base;ring

theorem purchased (N per:ℕ)(live:K<N)(child:ι→Fin 3)(g:ℝ)(g0:0<g)(g1:g≤1)
    (M0:∀a,0≤M a)(paper:∀a,1+wrapCost R (d a) (j a)≤wrap R (d a)*(H a)^2):
    (∑b,‖WilsonOriginalPublicTrialFigure.weight R (d ∘ child) g
      (fun i=>(vector R d j K target η M Y before reg N per) (child i)) b‖)≤
    ∏i,let a:=child i; base R d a*(H a)^2*M a*
      Real.exp ((height R (d a):ℝ)*s g+η*Real.log (R.family.S.a K/R.family.S.a (j a))⁻¹):=by
  apply roster R
  exact fun i=>single R d j K target η M Y before reg N per live (child i) g g0 g1 (M0 _) (paper _)

end YM.Integration.WilsonOlderFreshSoftTrialSalary
end
