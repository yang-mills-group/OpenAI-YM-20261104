import YM.Integration.WilsonCenteredNestedShadow

/-! Both complete deposited fields move by the same physical translation.
The freely situated parent need not coincide with any particular child. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedOrigin
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

lemma slide (P : Prescription F.sector.derivatives) (h : ℕ) (x : I→E4) (v : Labels S d) (o a : E4) :
    shadowOld P h (fun i=>x i+a) (o+a) v = shadowOld P h x o v ∧
    Q.packet h (fun i=>x i+a) v (o+a) = Q.packet h x v o := by
  constructor
  · unfold shadowOld shadow
    simp_rw [term_carry]
  · unfold Reader.packet
    simp_rw [Q.fresh_transport]

theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent)
    (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (v : Labels S d) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(k : ℕ)(B : ℝ),0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ (x:I→E4) (o:E4),WithinRoom r M η x o →
      ‖shadowOld P h x o v - Q.packet h x v o‖ ≤ B * shell r^k * r^((h:ℝ)+1-weight d) := by
  obtain ⟨k,B,Bn,close⟩ := WilsonCenteredNestedShadow.rooted F Q hp fac foundation lo ticket h v Mn ηp
  refine ⟨k,B,Bn,?_⟩
  filter_upwards [close] with r atR x o fit
  let y := fun i => x i-o
  have joined : WithinRoom r M η y 0 := by
    refine ⟨fun i=>by simpa only [y,sub_zero] using fit.span i,fun i j off=>?_⟩
    simpa only [y,sub_sub_sub_cancel_right] using fit.spaced i j off
  have shifts := slide F Q P h y v 0 o
  simp only [zero_add,y,sub_add_cancel] at shifts
  rw [shifts.1,shifts.2]
  exact atR y joined

end YM.Integration.WilsonCenteredNestedOrigin
