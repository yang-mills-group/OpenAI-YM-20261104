import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShieldedAtomVertex

/-! Sum every true loop/cubic/quartic interaction, including paths winding
around the original torus. No number-of-sites factor remains. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local UVNext.PricedKernels
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}
local notation "Fld" => Config G n

def atomMask (A:ℕ → Atom G k)(p:BudgetPoint)(W:Fld):ℝ:=
  (∑z:Site n,PathData.atomSeries A p W z)-uncut A W

def atomCash (k:ℕ)(σ C:ℝ)(D:ℕ):ℝ:=
  C*(2:ℝ)^(k+1)*Real.exp (-(σ/4)*(D:ℝ))*basin (σ/2)

private theorem unmasked_sums (A:ℕ → Atom G k){σ C:ℝ}(width:0<σ)
    (pay:SumBudget (fun i=>(A i).budget σ) C)(W:Fld)(z:Site n):
    Summable (fun i=>(A i).unmasked W z):=by
  refine (pay.2.1.mul_right ((2:ℝ)^k)).of_norm_bounded ?_
  intro i
  exact ((A i).unmasked_bound W z).trans (mul_le_mul_of_nonneg_right ((A i).lower_budget σ width) (by positivity))

theorem original_atom_mask_price (A:ℕ → Atom G k){σ C:ℝ}(width:0<σ)
    (pay:SumBudget (fun i=>(A i).budget σ) C)(p:BudgetPoint)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (out:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(s:Signed):
    |atomMask A p (pull s 0 U)-atomMask A p (pull s 0 V)|≤atomCash k σ C D:=by
  let w:=fun z:Site n=>Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ))
  let c:=(2:ℝ)^(k+1)*Real.exp (-(σ/4)*(D:ℝ))
  have cn:0≤c:=by dsimp only [c];positivity
  have cash:0≤C:=(tsum_nonneg pay.1).trans pay.2.2
  let diff:=fun z:Site n=>fun i:ℕ=>atomDefect (A i) p (pull s 0 U) z-atomDefect (A i) p (pull s 0 V) z
  have series(W:Fld)(z:Site n):HasSum (fun i=>atomDefect (A i) p W z)
      (PathData.atomSeries A p W z-(∑'i,(A i).unmasked W z)):=
    ((PathData.atom_dominated A p z width pay).summable W).hasSum.sub (unmasked_sums A width pay W z).hasSum
  let sumAt:=fun z:Site n=>(PathData.atomSeries A p (pull s 0 U) z-(∑'i,(A i).unmasked (pull s 0 U) z))-
    (PathData.atomSeries A p (pull s 0 V) z-(∑'i,(A i).unmasked (pull s 0 V) z))
  have ab(z:Site n):HasSum (diff z) (sumAt z):=(series _ z).sub (series _ z)
  have site(z:Site n):|sumAt z|≤(C*c)*w z:=by
    rw [←(ab z).tsum_eq]
    have price:∀i,‖diff z i‖≤(A i).budget σ*(c*w z):=fun i=> omitted_atom_price p e D U V out cold after s (A i) z width
    exact (norm_tsum_le_tsum_norm (ab z).summable.norm).trans (((ab z).summable.norm.tsum_le_tsum price (pay.2.1.mul_right _)).trans (by
      rw [tsum_mul_right];exact (mul_le_mul_of_nonneg_right pay.2.2 (mul_nonneg cn (Real.exp_pos _).le)).trans_eq (mul_assoc ..).symm))
  have geo:(∑z:Site n,w z)≤basin (σ/2):=
    (Equiv.sum_comp (turnSites s 0) (fun a:Site n=>Real.exp (-(σ/2)*(separation e.1 a:ℝ)))).le.trans (funnel (half_pos width) e.1)
  have eq:atomMask A p (pull s 0 U)-atomMask A p (pull s 0 V)=∑z:Site n,sumAt z:=by
    simp only [atomMask,uncut,sumAt,Finset.sum_sub_distrib]
  rw [eq]
  calc
    _ ≤ ∑z:Site n,|sumAt z|:=Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑z:Site n,(C*c)*w z:=sum_le_sum (fun z _=>site z)
    _ ≤ _:=by rw [←Finset.mul_sum];exact (mul_le_mul_of_nonneg_left geo (mul_nonneg cash cn)).trans_eq (by dsimp only [atomCash,c];ring)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
