import YM.Integration.WilsonReportingProductInvoice

/-! The centered signed price of a sum of booked fields belongs to the
intrinsic coefficient of that very sum on the same finite Wilson regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSignedReportSum

open Lattice Wilson RG OPE.Cards RG16 RG16.Literal Trace.Physical.GermGraph
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {I : Type} [Fintype I] [Nonempty I]

theorem assembled (H : C.Makes) (N p d u m : ℕ)
    (hu : Opened C d u p) (hm : Opened C d m p) (hum : u ≤ m) (hmN : m ≤ N)
    (t : ℕ) (ht : t ≤ N) (Y : I → Cut C N p) (fee : I → ℝ)
    (cont : ∀ i, Continuous (Y i))
    (bk : ∀ i, Booked C N p d (Y i) u (hum.trans hmN))
    (paid : ∀ i, PaidAt C.S N p t (C.beta N p) (fee i) (Y i -
      C.O N p (FilteredWilsonProduct.label (w:=(N,p)) H hu (hum.trans hmN) (Y i)) 0)) :
    Booked C N p d (∑ i, Y i) u (hum.trans hmN) ∧
    PaidAt C.S N p t (C.beta N p) (∑ i, fee i)
      ((∑ i, Y i) - C.O N p (master C N p d H m hm hmN
        (receipt C N p d H u m hu hm hum hmN (∑ i, Y i))) 0) := by
  have booked := IntrinsicProductLinearity.booked_sum C N p d u H hu (hum.trans hmN)
    (fun _ : I => (1:ℂ)) Y cont bk
  simp only [one_smul] at booked
  refine ⟨booked.1,?_⟩
  have combined := WilsonReportingProductInvoice.signed_sum H N p t ht _
    fee paid
  unfold receipt
  rw [dress_inverse,booked.2,map_sum]
  let L := (C.linearO N p d 0).mk' _
  rw [show C.O N p (∑ i, (C.factory d N p).terminal
      (topReport C N p d H u hu (hum.trans hmN) (Y i))) 0 =
      ∑ i, C.O N p ((C.factory d N p).terminal
        (topReport C N p d H u hu (hum.trans hmN) (Y i))) 0 from map_sum L _ _]
  rw [← Finset.sum_sub_distrib]
  exact combined

end YM.Integration.WilsonSignedReportSum
