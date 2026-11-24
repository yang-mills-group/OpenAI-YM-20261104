import YM.Integration.WilsonPhysicalHistoryGalleryRestore

/-! In the true pupil the previously registered painter multiplies the whole
correction on the same configurations. Its own summability is carried
separately from the small return paid by the old regular and forced rows. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryPictureRestore
open Lattice Wilson RG Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryCorrectionCarton
open scoped BigOperators Classical

variable {V T I J : Type*} [DecidableEq V] [Fintype V] [Countable I]
  {G : Gauge} {n : Side} {Z : Census V} {P : Rep G n} {o : V → Site n}
  (A : Gallery T I o P Z) (previous : Lamps T J G P.p o Z)
  (w : V → ℝ) (positive : ∀ v, 0 < w v)

abbrev picture : Gallery T (J ⊕ I) o P Z := ⟨previous.join A.E,A.K⟩

def retained (t : T) (U : Config G n) : Poly Z :=
  Poly.pass (previous.log t U) *
    restore P (WilsonPhysicalHistoryGroupedRegularReturn.single A t)
      (WilsonPhysicalHistoryGroupedForcedReturn.single A t) (regular A t) (forced A t) U

include positive in
theorem original {a q h : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid w P.p.B (a+2) q)
    (hard : A.K.Paid w P.p.B a h) (t : T) (U : Config G n)
    (issued : Summable (fun j => previous.frame j t U)) :
    (picture A previous).density t U = Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) *
      retained A previous t U := by
  have more : 0 ≤ a+2 := by linarith
  have earlier := reg.sums more positive t U
  have split : (picture A previous).density t U = Poly.pass (previous.log t U) * A.density t U := by
    change (Real.exp (P.exponent U) : ℂ) • (Poly.pass ((previous.join A.E).log t U) * A.gas t U) = _
    rw [Lamps.joinLog t U issued earlier, Extra.Trajectories.pass_add (Lamps.quiet_of_hasSum t U issued)
      (Lamps.quiet_of_hasSum t U earlier), Gallery.density, mul_smul_comm, mul_assoc]
  rw [split, WilsonPhysicalHistoryGalleryRestore.original A w positive expo reg hard t U]
  unfold retained
  ac_rfl

include positive in
theorem filed {a q h s C : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid w P.p.B (a+2) q)
    (hard : A.K.Paid w P.p.B a h) (t : T) (ω : V → ℝ) (pos : ∀ v, 0 < ω v)
    (spatial : 0 ≤ s) (whole : (picture A previous).E.Paid ω P.p.B s C) (U : Config G n) :
    (picture A previous).density t U = Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) *
      retained A previous t U := by
  apply original A previous w positive expo reg hard t U
  exact (whole.sums spatial pos t U).comp_injective (i:=Sum.inl) Sum.inl_injective

end YM.Integration.WilsonPhysicalHistoryPictureRestore
end

