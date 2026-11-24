import YM.Integration.WilsonConditionalTaylorThermalCensus
import YM.RGComparison.Core16.WilsonXLocal
import YM.RG02.Marker.Product

/-! The actual leading jet of the whole finite signed product of the compact
fields of an original family. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalBidScore
open Function Filter Lattice RG Tree Wilson Labels Source Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series
open PertExtension.GaussianScore Tested Radial Extra.Trajectories
open ThermalShortcuts.ThermalJets WilsonConditionalTaylorThermalStencil
open WilsonConditionalTaylorThermalCensus
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {c : Side} {I : Type} [Fintype I]
    (C : Family G) (D : I → ℕ) (i : ∀ j, (C.labels.level (D j)).Index)
    (bank : ∀ j, Bid.pop (C.localSection (D j)))
    {N p : ℕ} (d : Descent (C.side N p) c) (o : I → Site (C.side N p))

def entries (j : I) := recorded (bank j) (i j)

def weight := ∑ j, ((C.labels.level (D j)).grades (i j)).2

def source (part : Bool) (U : Config G (C.side N p)) :=
  Spool.look part (∏ j, (C.localSection (D j)).places (Pi.single (i j) 1) (o j) U)

include bank in
theorem accepted (makes : C.Makes) (part : Bool) :
    d.Testable (source C D i o part) ∧ d.grade (source C D i o part) (weight C D i) := by
  let O := fun j => (C.localSection (D j)).places (Pi.single (i j) 1) (o j)
  let w := fun j => ((C.labels.level (D j)).grades (i j)).2
  have bought (j : I) : d.Testable (O j) ∧ d.grade (O j) (w j) :=
    basis_test makes (bank j) d (o j) (i j)
  let K := RG02.Marks.full I
  let J : K.Mode := ⟨Finset.univ,Finset.mem_univ _⟩
  exact ⟨WilsonXLocal.tested (Spool.look part) (WilsonXLocal.products O K (fun j => (bought j).1) J),
    WilsonXLocal.wanted (Spool.look part) (WilsonXLocal.atGrade O K w (fun j => (bought j).2) J)⟩

theorem original (makes : C.Makes) (part : Bool) (x : Coordinates G d) :
    jet (source C D i o part ∘ d.fine 1 ∘ d.tablePath) (weight C D i) x =
      ∑ m ∈ rows (entries C D i bank), bill (entries C D i bank) part m *
        Law.product (fun r => leg G d (face (entries C D i bank) o r)
          (color (entries C D i bank) r)) (parties (entries C D i bank) m) x := by
  let S := entries C D i bank
  let φ := source C D i o part ∘ d.fine 1 ∘ d.tablePath
  have h := accepted C D i bank d o makes part
  have realJet := ((directions h.1.smooth x).shift (w:=weight C D i)
    (fun _ low => congrFun (jets_vanish h.1.smooth h.2 low) x)).tendsto_first
  have scales (r : ℝ) (z : ℂ) : Spool.look part ((r:ℂ)*z) = r * Spool.look part z := by
    rw [←Complex.real_smul,map_smul,smul_eq_mul]
  have he : Tested.germ ≤ 𝓝[≠] (0:ℝ) := nhdsWithin_mono _ fun _ ht => ne_of_gt ht
  have each := tendsto_finsetProd Finset.univ (fun j _ => (WilsonConditionalTaylorThermalStencil.original
    (S j) d (o j) x).mono_left he)
  have seen := ((Spool.look part).continuous.tendsto _).comp each
  have paid : Tendsto (fun r : ℝ => r⁻¹ ^ weight C D i * φ (r • x)) Tested.germ
      (𝓝 (Spool.look part (∏ j, head (S j) d (o j) x))) := by
    apply seen.congr'
    exact Filter.Eventually.of_forall fun r => by
      simp only [comp_apply, Finset.prod_mul_distrib, ←Finset.prod_pow_eq_pow_sum,
        ← Complex.ofReal_inv,← Complex.ofReal_pow,← Complex.ofReal_prod,scales,φ,source,weight]
  exact (tendsto_nhds_unique realJet paid).trans (polynomial S d o part x)

end YM.Integration.WilsonConditionalTaylorThermalBidScore
