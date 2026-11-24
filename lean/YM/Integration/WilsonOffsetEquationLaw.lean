import YM.FullVolume.Cross
import YM.UVExtension.Fallow.Micro

/-! The equation part selected by the physical run can be removed in a
signed expectation at any fine site. The genuine Wilson regulator,
regrading, projection and arbitrary bounded exterior are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetEquationLaw
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Push
open Next.Extract MergeProof PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge} {C : Family G} {d : ℕ}

def incoming (C : Family G) {d : ℕ} (V : SectionData (C.labels.level d))
    (N p : ℕ) (P : C.label d ≃ₗ[ℂ] C.label d) (x : C.label d) (o : Site (C.side N p)) :=
  initial V C.path N p (P.symm ((C.factory d N p).terminal.symm x)) o

theorem evaluated (V : SectionData (C.labels.level d)) (W : Mark.Weave G) (N p : ℕ)
    (P : C.label d ≃ₗ[ℂ] C.label d) (y : Label G d) (o : Site (C.side N p)) :
    incoming C V N p P (bindP C W d N p P y) o =
      ((C.S.a N:ℂ)^d)⁻¹ • (V.evaluate ((C.labels.level d).coords (W d y)) ∘ expandAt o) := by
  unfold incoming bindP Astar Mark.embedTo initial
  simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
  rw [show ∀ x:C.label d, (C.labels.level d).scaled (C.path.levels.clock.threshold N)⁻¹
    (Mark.tied C d N x) = x from (Mark.tied C d N).left_inv]
  rfl

theorem selected (R : Run G) (hG : G.Simple) :
    ∃ (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
      (P : ∀ d, (ℕ × ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d))
      (b : Presentation R.family),
      (∀ d, Mark.Portfolio R.family.params (V d) (W d)) ∧
      Hearthside R.family V W P b (Bandage.fly R.alloy.B.a) ∧
      ∀ d, ∃ radius : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ) (x : R.family.label d)
        (o : Site (R.family.side N p)) (X : Config G (R.family.side N p) → ℂ),
        LocalOn (Mark.Outer radius o) X → Envelope X →
        moment (R.family.beta N p) (fun U =>
          incoming R.family (V d) N p (P d (N,p)) (x - b.step d (N,p) x) o U * X U) = 0 := by
  obtain ⟨V,W,P,b,portfolio,issued⟩ := (R.again hG).1.receipts
  refine ⟨V,W,P,b,portfolio,issued,fun d => ?_⟩
  obtain ⟨r,M,vanish⟩ := Mark.radiusH W (V d) (portfolio d)
  refine ⟨r,?_⟩
  filter_upwards [Mark.lengths R.family.S M] with N size
  intro p x o X away bounded
  have member := (issued.foundation.step d N p).id_sub x
  obtain ⟨y,hy,raw⟩ := member
  change bindP R.family W d N p (P d (N,p)) y = x - b.step d (N,p) x at raw
  rw [← raw,evaluated]
  have active : 0 < R.family.beta N p :=
    (half_pos (zero_lt_one.trans (R.family.path.levels.fits.delayed _))).trans_le
      ((R.makes.wilson.represents N p N le_rfl).band.1)
  exact ((vanish y hy).scale (((R.family.S.a N:ℂ)^d)⁻¹))
    (R.family.side N p) (size p) o (R.family.beta N p) active.ne' X away bounded

end YM.Integration.WilsonOffsetEquationLaw
