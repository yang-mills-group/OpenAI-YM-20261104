import YM.Integration.WilsonGeneralArityCopyAccount
import YM.Integration.WilsonCapturedPrimaryPointIncome
import YM.Integration.WilsonOlderFreshLocatedBook

/-! The full group value of a published Copy, with every admitted thermal
grade and its zero-magnitude letters restored on the original physical site. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialCopyScalar
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor QuadraticLocal.Affinity
open WilsonOlderFreshGraphSlate WilsonOlderFreshGraphArmada WilsonOlderFreshGraphVote
open WilsonGeneralArityCopyAccount
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d Q : ℕ} {σ : ℝ} (T : Copy G d Q σ)
    (site : Site n) (g : ℝ) (U : Config G n)

def loan (a : Fin (Q+1)) (v : (T.roll a).Ty) : ℂ :=
  ((g^((a.val : ℤ)-((T.roll a).leg v).r) * ((T.roll a).leg v).atom.unmasked U site : ℝ) : ℂ)

theorem entire (sw : 0 ≤ σ) (a : Fin (Q+1)) :
    Summable (loan T site g U a) ∧
      (∑' v : {v : (T.roll a).Ty // 0 < ((T.roll a).leg v).atom.magnitude}, loan T site g U a v) =
        ∑' v : (T.roll a).Ty, loan T site g U a v := by
  let f := loan T site g U a
  let A := {v : (T.roll a).Ty | 0 < ((T.roll a).leg v).atom.magnitude}
  have support : Function.support f ⊆ A := by
    intro v occupied
    by_contra idle
    exact occupied (by simp [f,loan,WilsonOlderFreshGraphVote.factor T.roll idle U site])
  have kept : Summable (fun v : A => f v) := (absolute T site sw g U).sigma_factor a
  have posted := (hasSum_subtype_iff_of_support_subset support).mp kept.hasSum
  exact ⟨posted.summable,posted.tsum_eq.symm⟩

theorem original (E : Unit → Set ℂ) (t : Wallet E) (sw : 0 ≤ σ) :
    WilsonOlderFreshLocatedBook.word T site E t g U =
      value E t * ∑ a : Fin (Q+1), ∑' v : (T.roll a).Ty, loan T site g U a v := by
  let S := WilsonOlderFreshGraphPointWallet.point site
  have income := absolute T site sw g U
  have heard := income.hasSum.mul_left (value E t)
  have stamped : HasSum (fun z => (T.rows S E z).nominal g t U) (value E t * ∑'z, term T site g U z) :=
    heard.congr_fun fun z => T.group S E t g U z
  have paid := WilsonCapturedPrimaryPointIncome.uncut T S E t g U _ stamped
  change (QuadraticLocal.Spill.Foundry.uncut (T.rows S E) g t U).part S.mode = _
  rw [paid,income.tsum_sigma,tsum_fintype]
  exact congrArg (fun z => value E t*z) (sum_congr rfl fun a _ => (entire T site g U sw a).2)

end YM.Integration.WilsonCapturedPrimaryWeakTrialCopyScalar
