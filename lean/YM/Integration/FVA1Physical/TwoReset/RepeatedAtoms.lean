import YM.Integration.FVA1Physical.TwoReset.Period
import YM.QuadraticLocal.Poetry.Helmet

/-! Aliases in anchored stencils. Paths (including winding ones) are literally retained
with the same atoms. Only statements about unmasked jet identity use periodic replication. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Lattice RG AllOrder AllOrder.Haiku AllOrder.Ink AllOrder.Ker
open Laurent PertExtension.Series Stationary Finset QuadraticLocal QuadraticLocal.Poetry
open Further.PhysicalPeriodLimitF933 Macrame Shingle
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {V : Type} {c C : Side} {m k : ℕ}

/-- `gleam` is the stencil coupling coefficient before putting in the mask. -/
theorem gleam_convey (W : Window c C m) (L : Lantern G V) (y : Site C) (u : rule V c)
    (j d : ℕ) (a : Link G c) :
    Lantern.gleam L y (convey W u) j d (convey W a) =
      Lantern.gleam L (W.cut y) u j d a := by
  unfold Lantern.gleam
  split
  · let X := convey W (α:=Coarse G)
    have he : (fun z => L.light y (Stationary.input G C z) (convey W u)) ∘ X =
        fun z => L.light (W.cut y) (Stationary.input G c z) u := by
      funext z
      simp only [Function.comp_apply,X]
      rw [Haiku.billing]
      unfold Lantern.light Atom.unmasked
      rw [Echo.voice]
      unfold Slot.atSite
      rw [W.expansion]
    let f : Link G C → ℝ := fun z=> L.light y (Stationary.input G C z) (convey W u)
    have hf : ContDiffAt ℝ ω f 0 :=
      ((Helmet.frameGrade L.atom y).smooth).mul contDiffAt_const
    unfold Radial.jet
    rw [← he]
    rw [Next.Foundations.jets_linear X (hf.of_le le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- Coupling coefficient of the complete unmasked stencil supplied by these
rolls on period c. Later shown to be the *cover step*, not the finite-period step. -/
abbrev production (L : Fin k → Roll G V) (a : Link G c) (u : rule V c) (d : ℕ) : ℝ :=
  ∑ j : Fin k, ∑ x : Site c, ∑' i, Lantern.gleam ((L j).leg i) x u j.val d a

theorem production_convey (W : Window c C m) (L : Fin k → Roll G V) (a : Link G c)
    (u : rule V c) (d : ℕ) :
    production L (convey W a) (convey W u) d = m • production L a u d := by
  unfold production
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [gleam_convey]
  exact multiplied _ W.fold (fun x=> ∑' i,Lantern.gleam ((L j).leg i) x u j.val d a)

end YM.Integration.FVA1Physical.TwoReset
