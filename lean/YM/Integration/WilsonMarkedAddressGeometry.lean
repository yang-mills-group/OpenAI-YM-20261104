import YM.AnalyticBridge.VERIFIED_RESET_STEP.Rows
import YM.Integration.ActualWilsonTouchingVacuum
import YM.WilsonCoeffUV.Marked.Paths.RealExtent

/-! Connected covers of the native marked atom and its actual singleton
address stencils. Each connecting path is paid by the original lifted
source displacement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedAddressGeometry
open Function Finset Lattice Wilson RG Next.Scheduling AnalyticBridge.VerifiedReset
open WilsonCoeffUV WilsonCoeffUV.Mer.Rolls
open scoped Classical BigOperators
variable {I : Type} {G : Gauge} {r : ℕ} {n : Side}

private def bridge (x : Cover) : Slot := Extra.Iteration.slot x ⟨(0,1),by decide⟩

/-- The original mark positions may repeat or wrap. The valuation charges
each declared address once, just as the native fee does. -/
theorem joined (A : Atom G r) (z : I → Cover) (c : I) (J : Finset I)
    (B : ℕ) (hB : 0 < B) :
    B * coverNumber B (A.footprint (wrap n (z c)) ∪ J.biUnion (fun v => {wrap n (z v)})) ≤
      B*(1+2*r+6*J.card) + (A.length + feeH z c J) := by
  classical
  let o := wrap n (z c)
  let Y := A.footprint o
  let S (v : I) := Wages.walkCuts (bridge (z v-z c)) o
  have home : o ∈ Y := Finset.mem_image.mpr
    ⟨0, Finset.mem_insert_self .., by simp⟩
  have meets (v : I) : ¬Disjoint (S v) Y :=
    Finset.not_disjoint_iff.mpr ⟨o,root_in _ _,home⟩
  have address (v : I) : wrap n (z v) ∈ S v := by
    simpa [S,bridge,o,Work.F03.slotFace,map_sub] using
      (offset_inside (bridge (z v-z c)) o)
  have cover : coverNumber B (Y ∪ J.biUnion (fun v => {wrap n (z v)})) ≤
      coverNumber B Y + ∑ v ∈ J, coverNumber B (S v) := by
    apply le_trans (Corona.cover_mono (Finset.union_subset_union (Finset.Subset.refl Y) ?_) B)
      (ActualWilsonTouchingVacuum.cover S Y J B (fun v _ => meets v))
    intro y hy
    obtain ⟨v,hv,hyv⟩ := Finset.mem_biUnion.mp hy
    rw [Finset.mem_singleton.mp hyv]
    exact Finset.mem_biUnion.mpr ⟨v,hv,address v⟩
  have leg (v : I) :
      B*coverNumber B (S v) ≤ 6*B+Bank.terrain.gap (z c) (z v) := by
    have h := Wages.walked (bridge (z v-z c)) o B hB
    simp only [bridge,Extra.Iteration.slot_length] at h
    change B*coverNumber B (Wages.walkCuts (bridge (z v-z c)) o) ≤
      6*B+Laurent.size (z v-z c)
    change B*coverNumber B (Wages.walkCuts (bridge (z v-z c)) o) ≤
      2*B+(Laurent.size (z v-z c)+4) at h
    omega
  have hlegs := Finset.sum_le_sum (s := J) (fun v _ => leg v)
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hlegs
  have hgeom := Wages.traversed A o B hB
  change B*coverNumber B (Y ∪ J.biUnion (fun v => {wrap n (z v)})) ≤ _
  calc
    _ ≤ B*(coverNumber B Y + ∑ v ∈ J, coverNumber B (S v)) :=
      Nat.mul_le_mul_left B cover
    _ ≤ B+(r*(2*B)+A.length) + (J.card*(6*B)+∑ v ∈ J,Bank.terrain.gap (z c) (z v)) := by
      rw [Nat.mul_add,Finset.mul_sum]
      exact Nat.add_le_add hgeom hlegs
    _ ≤ _ := by unfold feeH; nlinarith only [Nat.zero_le J.card]

/-- The published torus centers can be substituted directly. -/
theorem centers (A : Atom G r) (J : Finset I) (c : I) (p : I → Site n)
    (z : I → Cover) (hc : wrap n (z c) = p c) (hz : ∀ v ∈ J, wrap n (z v) = p v)
    (B : ℕ) (hB : 0 < B) :
    B * coverNumber B (A.footprint (p c) ∪ J.biUnion (fun v => {p v})) ≤
      B*(1+2*r+6*J.card) + (A.length + feeH z c J) := by
  have he : J.biUnion (fun v => {wrap n (z v)}) = J.biUnion (fun v => {p v}) :=
    Finset.biUnion_congr rfl (fun v hv => congrArg (fun y : Site n => ({y} : Finset (Site n))) (hz v hv))
  simpa only [hc,he] using joined (n:=n) A z c J B hB

end YM.Integration.WilsonMarkedAddressGeometry
end
