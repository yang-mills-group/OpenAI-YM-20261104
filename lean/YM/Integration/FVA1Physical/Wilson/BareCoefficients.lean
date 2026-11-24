import YM.Integration.FVA1Physical.Wilson.ConditionalHistory
import YM.RGComparison.Core16.Spool.Transfer

/-! Physical Wilson coefficients for the bare top step in the qlocal free-link
coordinates. The field ray and the full vacuum use the same physical kernel,
and the source is the product of the actual stencils before conditional
integration. The estimate here is for this physical reading at fixed order. -/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Wilson

open YM.Lattice YM.RG YM.Tree YM.Precision
open YM.FVA2.CityHistory
open YM.RGComparison.Core16 YM.RGComparison.Core16.Spool
open YM.RGComparison.Core16.Parcel YM.RGComparison.Core16.Parcel.Oven
open YM.PertExtension.Series.Tested YM.PertExtension.Chart
open scoped Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)
    {ι : Type} [Fintype ι] (J : ι → Lamp G) (u : Pins G c) (p : ι → Site f)

/-- One real component of a full complex multi-insertion readout. The exponent
is the sum of engineering orders of all the insertions. -/
def relativeRead (b : Bool) (g : ℝ) : ℝ :=
  let β := fun _ : ℕ => g⁻¹ ^ 2
  let V := slice u g
  g⁻¹ ^ power J *
    (relativeTotal F Descent.nil β (look b ∘ column J p) V /
     relativeTotal F Descent.nil β 1 V)

theorem relativeRead_eq (h : S.patch.Branches S.kernel G) (b : Bool) (g : ℝ) :
    relativeRead F J u p b g = look b (reads J S u p g) := by
  let β := fun _ : ℕ => g⁻¹ ^ 2
  have hd : (Descent.push S F Descent.nil).OK G := ⟨h, trivial⟩
  have hcol : Continuous (column J p) := tally_cont J p
  have hc := (look b).continuous.comp hcol
  have hi : YM.Lattice.GaugeInvariant (look b ∘ column J p) :=
    fun k U => congrArg (look b) (tally_invariant J p k U)
  rw [descended J S u p g F (β := β) rfl, map_smul,
    ← WilsonXLocal.measured (look b) β hd hcol,
    (conditioned_relativeTotal F Descent.nil β hd hc hi (slice u g)).2]
  rfl

/-- All finite-order coefficients for the translated conditional quotient
are the physical `Fk.read` coefficients on the very lens used by FVA2. Coarse
directions, all site labels, the joint numerator and the conditional vacuum
are retained. -/
theorem relativeRead_expands {P : Oven S.patch} (X : P.Form G) (Z : ChartRatio G)
    (H : P.Offers X S.kernel) (h : Bid.Larger (G := G) S)
    (hu : ∀ i, ‖u i‖ ≤ X.Q) (hZ : LocalRatio Z) (b : Bool) :
    Aspiration (relativeRead F J u p b) (rankℝ J S F X Z u p b) := by
  rw [show relativeRead F J u p b = fun g => look b (reads J S u p g) from
    funext (relativeRead_eq F J u p h.1 b)]
  exact forecast J p b H h hu F hZ

/-- One truncation error constant across all admitted periods, forests, bounded
coarse directions and every placement of this finite family of stencils. -/
theorem relativeRead_uniform {M : Patch} {K : KernelChoices} {P : Oven M} {X : P.Form G}
    (H : P.Offers X K) (B : Lumen.Stage) (r : ℕ) (Z : ChartRatio G) (hZ : LocalRatio Z) :
    ∃ (U : Lumen.Stage) (C : ℝ), U.Above B ∧ 0 ≤ C ∧
      ∀ (c f : Side) (hd : f.val = c.val * M.L.val),
        let S : StepData c f := ⟨M, K, hd⟩
        Bid.Larger (G := G) S → ∀ (F : Forest S.ratio) (u : Pins G c) (p : ι → Site f),
          (∀ i, ‖u i‖ ≤ X.Q) →
          Price U r C (rank J S F X Z u p)
            (fun g => ⟨relativeRead F J u p false g, relativeRead F J u p true g⟩) := by
  obtain ⟨U, C, hU, hC, h⟩ := every J H B r hZ
  refine ⟨U, C, hU, hC, ?_⟩
  intro c f hd S hs F u p hu
  have eq : (fun g => Complex.mk (relativeRead F J u p false g) (relativeRead F J u p true g)) =
      reads J S u p := by
    funext g
    exact Complex.ext (relativeRead_eq F J u p hs.1 false g) (relativeRead_eq F J u p hs.1 true g)
  rw [eq]
  exact h c f hd hs F u p hu

end YM.Integration.FVA1Physical.Wilson

