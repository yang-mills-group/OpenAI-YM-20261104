import YM.Integration.WilsonCenteredNestedRotation

/-! Undo exactly one rotation on the whole raw field, at its actual root.
The bound is uniform in the rotation, the translated center, and the locations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedOrbit
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedLoggedRow WilsonCenteredNestedGross
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}

lemma field (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) (k : Ortho) :
    F.sector.turns.act h k (Q.packet h (Ortho.move k⁻¹ ∘x) (roll F.sector.turns k⁻¹ v) (Ortho.move k⁻¹ o)) =
    Q.packet h x v o := by
  rw [WilsonCenteredNestedRotation.packet F Q,←Q.law.group,mul_inv_cancel,Q.law.fixes]

theorem original {P : Prescription F.sector.derivatives} (hp : P.Coherent)
    (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u)
    (h : ℕ) (v : Labels S d) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j : ℕ)(A : ℝ),0 ≤ A ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(x:I→E4)(o:E4),WithinRoom r M η x o →
      ∀k:Ortho,‖spinning P F.sector.turns h x o k v - Q.packet h x v o‖ ≤
        wage j A r * r^((h:ℝ)+1-weight d) := by
  obtain ⟨j,B,Bn,price⟩ := WilsonCenteredNestedShadowBasis.original F Q hp fac foundation lo ticket h d Mn ηp
  obtain ⟨D,Dn,arms⟩ := WilsonCenteredNestedRotation.inputs F Q v
  obtain ⟨T,Tn,act⟩ := WilsonCenteredNestedRotation.output F Q h
  refine ⟨j,T*D*B,mul_nonneg (mul_nonneg Tn Dn) Bn,?_⟩
  filter_upwards [price,(show ∀ᶠr:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin)] with r offer rp x o fit k
  let y := Ortho.move k⁻¹ ∘ x
  let a := Ortho.move k⁻¹ o
  let w := roll F.sector.turns k⁻¹ v
  have seen := offer y a (WilsonCenteredNestedRotation.moved fit k⁻¹) w
  change ‖F.sector.turns.act h k (shadowOld P h y a w) - Q.packet h x v o‖ ≤ _
  rw [←field F Q h x v o k,←map_sub]
  have nonneg : 0 ≤ wage j B r * r^((h:ℝ)+1-weight d) := mul_nonneg
    (mul_nonneg Bn (pow_nonneg (zero_le_one.trans (shell_one r)) _)) (Real.rpow_nonneg rp.le _)
  calc
    _ ≤ T * ‖shadowOld P h y a w - Q.packet h y w a‖ := act k _
    _ ≤ T * (D * (wage j B r * r^((h:ℝ)+1-weight d))) :=
      mul_le_mul_of_nonneg_left (seen.trans (mul_le_mul_of_nonneg_right (arms k⁻¹) nonneg)) Tn
    _ = _ := by unfold wage;ring

end YM.Integration.WilsonCenteredNestedOrbit
