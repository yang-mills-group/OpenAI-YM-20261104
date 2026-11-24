import YM.QuadraticLocal.Class.Foundry
import YM.QuadraticLocal.Germ.Stock
import YM.MergeProof.Pitch

/-! Isolate the prescribed graph at an interior scale on its original physical
vacuum. The numerical forced coefficients, their eligibility and their scalar
gas are retained. Only the already accumulated *marked* residual is omitted. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect

open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn Ac
open Push.AbsoluteSums Fusion Fusion.Attached ConnectedActivityE6
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V ι μ X : Type} [DecidableEq V] {Γ : Census V}
    {A : Passport n V} {P : Rep G n} {w : V → ℝ} {k : ℝ}

/-- Obtain the *same* unmarked forced array from the previously issued
signed input, without a new tariff or an assumption about the unmarked gas. -/
theorem originalHard (E : Tint.Incoming A P X μ Γ) (x : X) (hw : ∀ v, 0 < w v)
    (paid : E.hard.Paid w P.p.B P.p.supportExponent k) :
    Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k :=
  Hard.transfer E.hard P.p.supportExponent x paid hw

/-- Zero prior marked errors on the original physical representation, with
every original scalar K still in place on its original forced support. -/
def modelInput (A : Passport n V) (P : Rep G n) (Γ : Census V) (X : Type)
    (h : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k) :
    Tint.Incoming A P X Empty Γ :=
  ⟨Spill.Foundry.noneL (α:=X) (R:=Γ) P A.origin, Hard.rent h⟩

theorem model_input_prices (h : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (w : V → ℝ) :
    (modelInput A P Γ X h).old.Paid w P.p.B P.p.supportExponent 0 ∧
      (modelInput A P Γ X h).hard.Paid w P.p.B P.p.supportExponent k :=
  ⟨Spill.Foundry.empty_lit P _ _ _, Hard.leasing h⟩

theorem model_input_addresses {T : V → Type} [∀ v, AddCommGroup (T v)] [∀ v, Module ℝ (T v)]
    (allow : ∀ v, Set (T v)) (kills : ∀ v, Submodule ℝ (T v))
    (h : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k) :
    Affinity.Taut A.support allow kills (modelInput A P Γ (Affinity.Wallet allow) h).old ∧
      Affinity.Crown A.support allow kills (modelInput A P Γ (Affinity.Wallet allow) h).hard := by
  refine ⟨⟨fun i => i.elim,fun i => i.elim⟩,⟨?_⟩⟩
  intro i U
  refine Affinity.Stencil.const (Poly.bead Γ ((P.activities.K i U : ℝ) : ℂ)) ?_
  intro s hs
  exact (Poly.part_send ..).trans (if_neg hs)

variable [Fintype V]

omit [Fintype V] in
/-- The complete marked gas of the model-only input is precisely the physical
scalar gas, including on failed configurations where it need not be one. -/
theorem model_input_gas (h : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (hw : ∀ v, 0 < w v) (x : X) (U : Config G n) :
    (∑' j, packet P.activities P.p ((modelInput A P Γ X h).hard.hard x) U j) =
      Poly.bead Γ ((P.activities.gas P.p U : ℝ) : ℂ) := by
  let H := (modelInput A P Γ X h).hard
  have summed := Hard.packet_summing H (Hard.leasing (w:=w) h) P.p.exponent_pos.le hw x U
  have one j : packet P.activities P.p (H.hard x) U j =
      Poly.bead Γ ((P.activities.gasOccurrence P.p j U : ℝ) : ℂ) := by
    unfold packet Activities.gasOccurrence
    split
    · rw [Complex.ofReal_prod, map_prod]; rfl
    · simp
  ext s
  by_cases hs : s = Γ.quiet
  · subst s
    exact (Hard.packet_of_quiet H x U summed).trans ((Poly.part_send ..).trans (if_pos rfl)).symm
  · rw [Poly.share summed]
    change (∑' j, (packet P.activities P.p (H.hard x) U j).part s) = _
    simp_rw [one]
    change (∑' j, (Poly.send Γ.quiet _).part s) = (Poly.send Γ.quiet _).part s
    simp_rw [Poly.part_send,if_neg hs,tsum_zero]

/-- Exact all-field source for the prescribed *already dressed* library M on
the current vacuum. No assertion about the size of a signed prior remainder
is needed to form this new input. -/
theorem model_input_field (M : ι → Row A Γ G X)
    (h : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (hw : ∀ v, 0 < w v) (x : X) (U : Config G n)
    (summed : Summable (fun i => (rendered M P.p (Coat.gStep P.beta)).frame i x U)) :
    (Tint.Patrol.picture M (modelInput A P Γ X h)).density x U =
      (P.eval U : ℂ) • Poly.pass ((rendered M P.p (Coat.gStep P.beta)).log x U) := by
  let S := modelInput A P Γ X h
  let L := rendered M P.p (Coat.gStep P.beta)
  have hs : (Tint.Patrol.picture M S).E.log x U = L.log x U := by
    change (L.join S.old).log x U = _
    rw [Lamps.joinLog x U summed (hasSum_fintype _).summable,
      show S.old.log x U = 0 from tsum_empty,add_zero]
  have gas := model_input_gas (A:=A) (Γ:=Γ) h hw x U
  rw [Gallery.density,hs]
  change (Real.exp (P.exponent U) : ℂ) • (Poly.pass (L.log x U) *
    (∑' j,packet P.activities P.p (S.hard.hard x) U j)) = _
  rw [gas,mul_comm (Poly.pass _),Poly.product_bead,smul_smul,Rep.eval,Complex.ofReal_mul]

end YM.Integration.WilsonPhysicalMarkedDefect

