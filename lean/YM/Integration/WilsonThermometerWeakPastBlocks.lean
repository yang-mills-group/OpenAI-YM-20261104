import YM.Integration.WilsonThermometerWeakMixedCells

/-! Prices for the finite number of additional genuine physical meshes needed
to house the two independent signed weak observations in distinct cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPastBlocks
open PhysicalNext.Repeat.Legato Filter Set Lattice RG Push Next.Rank MergeProof Next.Rank.East
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.alloy.B.a

private theorem log_price {z:ℝ} (pos:0<Real.log z) (large:2≤Real.log (Real.log z)):
    1+Real.log (2+Real.log z)≤Real.exp (Real.log (Real.log z)^2):=by
  have two:2≤Real.log z:=by
    calc
      _ ≤ 1+Real.log (Real.log z):=by linarith
      _ ≤ Real.log z :=by simpa [Real.exp_log pos,add_comm] using Real.add_one_le_exp (Real.log (Real.log z))
  have comparison:=Real.log_le_log (by linarith:0<2+Real.log z) (show 2+Real.log z≤2*Real.log z by linarith)
  rw [Real.log_mul (by norm_num) pos.ne'] at comparison
  have fixed:Real.log 2≤1:=by have h:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num);norm_num at h;exact h
  have exp:=Real.add_one_le_exp ((Real.log (Real.log z))^2)
  nlinarith [sq_nonneg (Real.log (Real.log z)-2)]

theorem paid (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b):
    ∀ᶠ k:ℕ in atTop, ∀ j≤k,(((A).S.block j).val:ℝ)≤(A).clock.monitor k:=by
  let z:=fun k=>(A).clock.hatBeta k
  have high:Tendsto z atTop atTop:=Trace.Terrace.hrate (A) simple
  have logstate:=Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp high)
  have hz:∀ᶠ k in atTop,1<z k:=high.eventually (eventually_gt_atTop 1)
  obtain ⟨j₀,future⟩:=eventually_atTop.mp hz
  have monitor:Tendsto (A).clock.monitor atTop atTop:=
    Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by norm_num:2≠0)).comp logstate)
  have early:∀ j∈Finset.range j₀,∀ᶠ k in atTop,(((A).S.block j).val:ℝ)≤(A).clock.monitor k:=
    fun j _=>monitor.eventually_ge_atTop _
  filter_upwards [((Finset.eventually_all (Finset.range j₀)).2 early),logstate.eventually_ge_atTop 2] with k finite large j hj
  by_cases hj₀:j<j₀
  · exact finite j (Finset.mem_range.mpr hj₀)
  · have pos:1<z j:=future j (le_of_not_gt hj₀)
    have mono:=Trace.Terrace.monoBeta (A) simple hj
    have logbase:=Real.log_le_log ((zero_lt_one).trans pos) mono
    have nonneg:=Real.log_pos pos
    calc
      _ ≤ 1+Real.log (2+Real.log (z j)):=shop.preMesh j
      _ ≤ 1+Real.log (2+Real.log (z k)):=by
        have a:=Real.log_le_log (by linarith:0<2+Real.log (z j)) (show 2+Real.log (z j)≤2+Real.log (z k) from by linarith)
        linarith only [a]
      _ ≤ _:=log_price (nonneg.trans_le logbase) large

theorem earlier (S:Schedule) (n:ℕ) {k:ℕ} {u:ℝ} (pos:1≤u)
    (paid:∀j≤k,((S.block j).val:ℝ)≤u):∀j≤k,S.a (j-n)≤u^n*S.a j:=by
  induction n with
  | zero=>intro j _;simp
  | succ n ih=>
    intro j hj
    cases j with
    | zero=>simp only [Nat.zero_sub];exact le_mul_of_one_le_left (S.a_pos _).le (one_le_pow₀ pos)
    | succ j=>
      rw [Nat.succ_sub_succ_eq_sub,pow_succ,S.a_step]
      have pay:=paid j (by omega)
      have fee:0<((S.block j).val:ℝ):=by exact_mod_cast (S.block j).property
      calc
        _ ≤ u^n*S.a j:=ih j (by omega)
        _ ≤ u^n*(u*(S.a j/((S.block j).val:ℝ))):=by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) _)
          rw [←mul_div_assoc,le_div_iff₀ fee];exact (mul_le_mul_of_nonneg_left pay (S.a_pos j).le).trans_eq (mul_comm ..)
        _ = _ :=(mul_assoc ..).symm

end YM.Integration.WilsonThermometerWeakPastBlocks
end
