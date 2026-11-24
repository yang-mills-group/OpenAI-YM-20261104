import YM.Integration.WilsonThermometerOriginalPanelDates
import YM.UVExtension.Fallow.Micro

/-! The actual selected Wilson equation section vanishes in displaced
microscopic measurements. Its finite-dimensional source radius is fixed
before the ultraviolet cutoff, the period and the offset-dependent vector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerEquationDisplacements
open Function Filter Set MeasureTheory Lattice Wilson RG Labels Source Bid Cells
open PhysicalNext.Repeat.Legato WilsonLimitConstruction MergeProof Push Push.Mark
open Extraction Extraction.Lease Next.Extract Org
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "C" => R.family

theorem original (simple : G.Simple) :
    ∃ (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G), ∃ U e,
      (∀ d, Mark.Portfolio R.family.params (V d) (W d)) ∧
      Hearthside C V W U e (Bandage.fly R.alloy.B.a) ∧
      ∀ d, ∃ r : ℕ, ∀ᶠ N : ℕ in atTop, ∀ p (v : R.family.label d),
        (R.family.factory d N p).terminal v ∈ Mark.carrier C W d N p →
        ∀ o : Site (R.family.side N p), ∀ {I : Type} [Fintype I]
          (q : I → R.family.book.Token) (a : I → Site (R.family.side N p)),
          (∀ i, ↑((R.family.localSection (q i).1).footprint (a i)) ⊆ Mark.Outer r o) →
          moment (R.family.beta N p) (fun u => initial (V d) R.family.path N p v o u *
            ∏ i, R.family.seen (q i) (a i) u)=0 := by
  obtain ⟨V,W,U,e,supplied,hearth⟩ := (R.again simple).1.receipts
  refine ⟨V,W,U,e,supplied,hearth,fun d => ?_⟩
  obtain ⟨r,M,stock⟩ := Mark.radiusH W (V d) (supplied d)
  refine ⟨r,?_⟩
  filter_upwards [Mark.lengths R.family.S M] with N sides p v kernel o I inst q a clear
  obtain ⟨y,hy,origin⟩ := Mark.obtained W _ kernel
  let z := (((R.family.S.a N : ℂ)^d)⁻¹)
  have filed : initial (V d) R.family.path N p v o =
      z • ((V d).evaluate ((R.family.labels.level d).coords (W d y)) ∘ expandAt o) := by
    unfold initial Mark.embedTo at *
    simp only [LinearEquiv.trans_apply] at origin
    rw [show v = _ from (R.family.factory d N p).terminal.injective origin]
    let F := R.family.labels.level d
    let t := R.family.path.levels.clock.threshold N
    rw [show ∀ x : R.family.label d, F.scaled t⁻¹ (Mark.tied C d N x)=x from
      (Mark.tied C d N).left_inv]
    rfl
  let B (u : Config G (R.family.side N p)) := ∏ i, R.family.seen (q i) (a i) u
  have localB : LocalOn (Mark.Outer r o) B := by
    intro u u' h
    exact Finset.prod_congr rfl (fun i _ => R.family.localO N p (q i).1 (q i).2
      (a i) u u' (agrees_mono h (clear i)))
  have good : RG.Envelope B := Mark.cont_envelope (continuous_finsetProd Finset.univ
    (fun i _ => R.family.continuousO N p (q i).1 (q i).2 (a i)))
  have βpos : 0 < R.family.beta N p :=
    (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed _))).trans_le
      (R.makes.wilson.represents N p N le_rfl).band.1
  rw [filed]
  exact ((stock y hy).scale z) _ (sides p) o _ βpos.ne' B localB good

end YM.Integration.WilsonThermometerEquationDisplacements
