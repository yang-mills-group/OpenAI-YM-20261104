import YM.Integration.WilsonAddressedEquationAtWindow
import YM.Integration.WilsonAddressedEquationMoments
import YM.Integration.WilsonAddressedEquationOrbit

/-! The weak-date price on a bounded original reported label. The radius
of the label ball is fixed before the cutoff and may belong to that report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedEquationAllowance
open Function Filter Finset Lattice Wilson RG Labels Source Push Extraction MergeProof
open Next.Extract Push.RelayDifference Extra.Histories Extra.Histories.Motion FullVolume Bid PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {d:ℕ}
variable {V:∀ t,SectionData (C.labels.level t)} {W:Mark.Weave G}
  {P:∀ t,(ℕ×ℕ) → (C.label t ≃ₗ[ℂ] C.label t)} {b:Presentation C} {ζ:ℕ→ℕ→ℝ}
set_option quotPrecheck false
local notation "F"=> C.labels.level d

theorem paid (real:C.Makes) (house:Hearthside C V W P b ζ) {E:ℕ→ℝ} {U}
    (stamp:Hearth (C:=C) (V d) ζ E (fun N p=>P d (N,p)) U) (A:ℝ) :
    ∀ᶠ N:ℕ in atTop, ∀ p:ℕ, ∀ x:C.label d, ‖x‖ ≤ A → ∀ w:ℕ,
      orbitCost (F) * (F).coeffSize ((P d (N,p)).symm
        ((C.factory d N p).terminal.symm (x-b.step d (N,p) x))) * abs (E N) / gainChart C.path N w ≤
        (2*Fintype.card (F).Index*orbitCost (F)) *
        Real.exp (C.S.scale w/8-3*C.S.scale N/32) := by
  obtain ⟨B,control⟩ := house.uniform d
  have old : ∀ᶠ N:ℕ in atTop, ∀ p:ℕ, ‖E N‖ ≤ flight C (1/64) (N,p) :=
    FullVolume.late.mp ((borrowed (stamp.coined Order.full)) (1/64) (by norm_num))
  filter_upwards [old,Work.D01.terminal_ball C real d ((1+abs B)*abs A) (1/64) (by norm_num),
    stamp.stamped] with N old bounds measured
  intro p x ball w
  have op : ‖b.step d (N,p) x‖ ≤ abs B*abs A :=
    ((b.step d (N,p)).le_opNorm _).trans (mul_le_mul ((control (N,p)).trans (le_abs_self _))
      (ball.trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _))
  have small : ‖x-b.step d (N,p) x‖ ≤ (1+abs B)*abs A := by
    have h := norm_sub_le x (b.step d (N,p) x)
    linarith only [h,ball.trans (le_abs_self A),op]
  let v := (C.factory d N p).terminal.symm (x-b.step d (N,p) x)
  let T := Real.exp ((1/64:ℝ)*C.S.scale N)
  have terminal : ‖v‖ ≤ T := bounds p _ small
  have size : (F).coeffSize v ≤ (Fintype.card (F).Index:ℝ)*T := by
    calc
      (F).coeffSize v = ∑ i:(F).Index, ‖v i‖ := rfl
      _ ≤ ∑ _i:(F).Index, T := Finset.sum_le_sum fun i _ => (norm_le_pi_norm v i).trans terminal
      _ = _ := by simp
  have source : (F).coeffSize ((P d (N,p)).symm v) ≤ 2*((Fintype.card (F).Index:ℝ)*T) :=
    ((measured p).2.1 v).trans (mul_le_mul_of_nonneg_left size (by norm_num))
  have quiet : abs (E N) ≤ T := by simpa only [T, flight, Real.norm_eq_abs] using old p
  have cost : 0 ≤ orbitCost (F) := (zero_le_one.trans (orbitCost_one_le _))
  have priced := mul_le_mul (mul_le_mul_of_nonneg_left source cost) quiet (abs_nonneg _)
    (mul_nonneg cost (by positivity))
  have pass := div_le_div_of_nonneg_right priced (Real.exp_pos (1/8*(C.S.scale N-C.S.scale w))).le
  change orbitCost (F)*(F).coeffSize ((P d (N,p)).symm v)*abs (E N)/gainChart C.path N w ≤ _
  refine pass.trans_eq ?_
  change orbitCost (F)*(2*((Fintype.card (F).Index:ℝ)*T))*T /
    Real.exp (1/8*(C.S.scale N-C.S.scale w))=_
  rw [show C.S.scale w/8-3*C.S.scale N/32 =
      (1/64)*C.S.scale N+(1/64)*C.S.scale N-1/8*(C.S.scale N-C.S.scale w) by ring,
    Real.exp_sub,Real.exp_add]
  dsimp only [T]
  ring

end YM.Integration.WilsonAddressedEquationAllowance
