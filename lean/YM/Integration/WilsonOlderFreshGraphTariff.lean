import YM.Integration.WilsonOlderFreshGraphWallet

/-! Extract the full unweighted before-test salary from one publication.
The same number works for every cutoff, every finite side, every film in the
registered test ball and all coupling grades in the finite section. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphTariff
open Function Filter Finset Lattice Laurent RG Wilson Marker Gauge
open Push Push.AbsoluteSums Paths Animals ConnectedActivityE6 QuadraticLocal QuadraticLocal.Sunrise
open QuadraticLocal.Poetry QuadraticLocal.Earn QuadraticLocal.Mentor AllOrder AllOrder.Ink AllOrder.Floe
open scoped Classical BigOperators Topology
variable {G:Gauge}{Q d:ℕ}{ι:Type} (I:Unit→Loan) (level:(I ()).toll=d)
variable (W:Fin (Q+1)→ι→Poetry.Roll G Unit) (σ:ℝ) (test:ι→ℝ)
include level in
theorem original (published:∀j:Fin (Q+1),Agenda.Booked {()} () I (W j) test j.val (2*σ) 1):
    ∃ B:ℝ,0 ≤ B ∧ ∃ C:Fin (Q+1)→ι→ℝ,
      (∀j,Money.CreditF test 1 (C j)) ∧
      (∀j p,(W j p).Faith {()} () (j.val+d+2) (2*σ) (C j p) ∧ (W j p).honest) ∧
      ∀p,(∑j,C j p) ≤ B*(1+|test p|):=by
  choose C bound roll using published
  choose h pos earn using bound
  refine ⟨∑j,h j,Finset.sum_nonneg (fun j _=>pos j),C,?_,?_,?_⟩
  · exact fun j=>⟨h j,pos j,earn j⟩
  · intro j p
    simpa [Agenda.guard,Aviary.plusK,level] using roll j p
  · intro p
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _=>by simpa using (earn j p).2
end YM.Integration.WilsonOlderFreshGraphTariff
end
