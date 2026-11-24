import YM.Integration.WilsonCenteredNestedSharedField

/-! Finite input and terminal-output wallets on the actual single
rotation and real branch fixed by the original final. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedOrbitWallet
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedTerminalOrbit WilsonCenteredNestedProjectedShadow
open WilsonCenteredNestedSharedField WilsonCenteredNestedShadowBasis
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

include Q in
theorem input (v:Fin 3→S.Tag) : ∃ B:ℝ, 0≤B ∧ ∀k b,
    mass (voices (entrants F v k b))≤B := by
  obtain ⟨B,Bn,rot⟩ := WilsonCenteredNestedRotation.inputs F Q (voices v)
  obtain ⟨A,_,barred⟩ := WilsonCenteredNestedRotation.inputs F Q (bar F.room.kernel.spin (voices v))
  refine ⟨max B A,Bn.trans (le_max_left ..),fun k b=>?_⟩
  cases b
  · have hh : voices (entrants F v k false)=roll F.sector.turns k⁻¹ (voices v) := by funext i; rfl
    rw [hh]
    exact (rot k⁻¹).trans (le_max_left ..)
  · have hh : voices (entrants F v k true)=roll F.sector.turns k⁻¹ (bar F.room.kernel.spin (voices v)) := by funext i; rfl
    rw [hh]
    exact (barred k⁻¹).trans (le_max_right ..)

theorem output (m:ℕ) (c:Q.channels m) : ∃ T:ℝ,0≤T ∧ ∀(k:Ortho)(b:Bool)(v:S.Field m),
    ‖read F Q m m c (out F m k b v)‖≤T*‖v‖ := by
  obtain ⟨L,Ln,rot⟩:=WilsonCenteredNestedRotation.output F Q m
  let readout := (read F Q m m c).toContinuousLinearMap
  let mirror := (conjugateR F.room.kernel.spin m).toContinuousLinearMap
  let A := max 1 ‖mirror‖
  have An : 0≤A := zero_le_one.trans (le_max_left ..)
  refine ⟨‖readout‖*(A*L),mul_nonneg readout.opNorm_nonneg (mul_nonneg An Ln),fun k b v=>?_⟩
  have seen : ‖out F m k b v‖≤A*(L*‖v‖) := by
    cases b
    · exact (rot k v).trans (le_mul_of_one_le_left (mul_nonneg Ln (norm_nonneg _)) (le_max_left ..))
    · change ‖mirror (F.sector.turns.act m k v)‖ ≤ _
      exact (mirror.le_opNorm _).trans (mul_le_mul (le_max_right ..) (rot k v) (norm_nonneg _) An)
  exact (readout.le_opNorm _).trans ((mul_le_mul_of_nonneg_left seen readout.opNorm_nonneg).trans_eq (by ring))

lemma scalar_norm (b:Bool) (z:ℂ) : ‖scalar b z‖=‖z‖ := by cases b <;> simp [scalar]

end YM.Integration.WilsonCenteredNestedOrbitWallet
