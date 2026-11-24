import YM.Integration.WilsonReportHarvestResidentLog

/-! Cost of an entire supported coefficient difference at a single actual occupied site. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentRootFee
open Function Finset Set Lattice RG Marker Wilson Push AbsoluteSums MergeProof Accent GridApprox.Nil
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{J:Census V}
variable {F:Support n → Config G n → Poly J}{B:ℕ}{α δ:ℝ}

theorem rooted (bank:Towed (fun _:V => (1:ℝ)) id F B α δ)(lp:0 ≤ α)
    (s:J.Mode)(x:Site n)(U:Config G n)(here:∀X,(F X U).part s≠0 → x∈X):
    (∑X,‖(F X U).part s‖) ≤ δ ∧ ‖∑X,(F X U).part s‖ ≤ δ:=by
  obtain ⟨wallet,_,hit,atoms⟩:=bank
  let wp:=fun _:V=> (zero_lt_one:0<(1:ℝ))
  have bill:=hit x
  have cost:SumBudget (fun X:Support n=>‖(F X U).part s‖) δ:=by
    apply budget_mono bill
    · intro X;exact norm_nonneg _
    intro X
    by_cases zero:(F X U).part s=0
    · rw [zero,norm_zero];exact bill.1 X
    have fare:‖(F X U).part s‖ ≤ wallet X:=by
      simpa [Poly.toll] using (Poly.member wp s _).trans ((atoms X).fares wp |>.2 U)
    change _ ≤ if x∈X then wallet X*Real.exp (α*(coverNumber B X:ℝ)) else 0
    rw [if_pos (here X zero)]
    exact fare.trans (le_mul_of_one_le_right ((atoms X).fares wp).1 (Real.one_le_exp (mul_nonneg lp (Nat.cast_nonneg _))))
  have all:=cost.2.2
  rw [tsum_fintype] at all
  exact ⟨all,(norm_sum_le _ _).trans all⟩

theorem purchased {o:V → Site n}{t:ℝ}
    (bank:Towed (fun _:V => (1:ℝ)) id F B α δ)(lp:0 ≤ α)(scope:∀X,Borne o X (F X) t)
    (s:J.Mode)(v:V)(inMode:v∈s.val)(U:Config G n):
    (∑X,‖(F X U).part s‖) ≤ δ ∧ ‖∑X,(F X U).part s‖ ≤ δ:=by
  apply rooted bank lp s (o v) U
  intro X nz
  by_contra away
  apply nz
  exact (scope X).scope U s (fun included=>away (included inMode))

end YM.Integration.WilsonReportHarvestResidentRootFee
