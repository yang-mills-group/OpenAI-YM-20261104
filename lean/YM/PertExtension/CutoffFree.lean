import YM.PertExtension.FreePrescription
import YM.PertExtension.AverageGrid

/-! Top Gaussian answer from the finite diagonal prescription on a joint
real position-space compactly supported test before additional position
frame mixing. Complex tests by linearity are not needed by the following
real-array prescription. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.LatticePT.CutoffFree
open Function Filter Set Wilson Lattice RG MeasureTheory Orb Gauge MvPolynomial Finset Next.Rank Next.Rank.Normal Maxwell
open Source Labels Slope Mixed Leading Node Screens Configuration
open scoped ContDiff Topology BigOperators Classical
variable {G: Gauge}{n:ℕ}(v : Fin n→LatticePT.Word G)(q : ℕ+)(hq:1<q.val)
variable (Ψ:Points n→ℝ){K : Set (Points n)}(hK:IsCompact K)(hc:K⊆conf n)(hz:Function.support Ψ ⊆ K) (ht:Continuous Ψ)

abbrev realTyped:=fun x:Points n=> Ψ x * (electricity v x).re
def arrayAt (t:ℕ)(k:Native q t)(s:Grid.offsets q n t):ℝ:= Ψ (Grid.sample q t s) * Price.ticket v q t (Price.orig q t k) (lift ∘ s)
def kernel (i : ℕ)(z:Native q i):ℝ :=epsilon q i ^ (4*n) * ∑ s, arrayAt v q Ψ i z s

lemma all_energies (m:ℕ): polynomialTop v q m (Ψ∘points) 0 = ((origins q m).card:ℝ)⁻¹ * ∑ z∈origins q m,kernel v q Ψ m z := by
   rw [Price.diag_read]; simp only [Fintype.card_fin,kernel,arrayAt,Mixed.price,Function.comp_apply];rw [Finset.sum_comm];simp only [mul_sum];exact sum_congr rfl fun i hi=>sum_congr (by ext1; simp) fun j hj=> by rw [Grid.sample_eq];ring -- careful using `simp ←sum_comm` loops
include hK hz hc ht hq
lemma charged (w:(t:ℕ)→Native q t)(hw:∀ t,w t∈origins q t): Integrable (realTyped v Ψ) ∧ Tendsto (fun i:ℕ=> kernel v q Ψ i (w i)) atTop (𝓝 (∫ x:Points n,realTyped v Ψ x)):= by
    have hzero x (hx:x∉K):Ψ x=0 := notMem_support.mp (fun ha=>hx (hz ha))
    refine Grid.integrable_spots hq (F:=fun i=>arrayAt v q Ψ i (w i)) ?_ hK (fun k s hs=>by simp [arrayAt,hzero _ hs]) fun x hx=>by simp [realTyped,hzero _ hx]
    intro s x hx hs; exact (ht.continuousAt.tendsto.comp hs).mul (ticket_limit v q hq w hw s (hc hx) hs)

theorem profile_limit : Integrable (realTyped v Ψ) ∧ Tendsto (fun m:ℕ=>polynomialTop v q m (Ψ∘points) 0) atTop (𝓝 (∫ x:Points n,realTyped v Ψ x)):=by
   choose w hw using fun t=> hasOrigin q t
   constructor
   · exact (charged v q hq Ψ hK hc hz ht w hw).1
   simp_rw [all_energies]
   exact Grid.average_paths (hn:=fun m=>hasOrigin q m) fun v hv=> (charged _ _ hq _ hK hc hz ht v hv).2
end YM.PertExtension.LatticePT.CutoffFree
