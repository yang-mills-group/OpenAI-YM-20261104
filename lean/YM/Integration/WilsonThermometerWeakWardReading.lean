import YM.Integration.WilsonThermometerWeakEquationCost

/-! One fixed probing field on the original finite Wilson law. Two measured
labels with the same projection differ in this reading by precisely the
rooted, unprojected original equation residual against the same probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWardReading
open Function Filter Set MeasureTheory Lattice Wilson RG Source Push Extraction FullVolume
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat.Legato
open WilsonOffsetReportingProducts WilsonOffsetEquationLaw WilsonAddressedCollarEquations WilsonAddressedEquationShelf
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "C" => R.family

private theorem integrable {N p:ℕ} {f:Config G ((C).side N p)→ℂ} (h:Continuous f):
    Integrable f (law G _ ((C).beta N p)) :=
  h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def read (d N p:ℕ) (o:Site ((C).side N p)) (X:Config G ((C).side N p)→ℂ) (test:Continuous X) :
    (C).label d →ₗ[ℂ] ℂ where
  toFun x:=moment ((C).beta N p) (fun U=>(C).O N p x o U*X U)
  map_add' x y:=by
    have linear:=(((C).linearO N p d o).mk' _).map_add x y
    change (C).O N p (x+y) o=(C).O N p x o+(C).O N p y o at linear
    simp only [linear,Pi.add_apply,add_mul,moment]
    exact integral_add (integrable R (((C).continuousO N p d x o).mul test))
      (integrable R (((C).continuousO N p d y o).mul test))
  map_smul' c x:=by
    have linear:=(((C).linearO N p d o).mk' _).map_smul c x
    change (C).O N p (c • x) o=c • (C).O N p x o at linear
    simp only [linear,Pi.smul_apply,smul_eq_mul,mul_assoc,moment,integral_const_mul,RingHom.id_apply]

variable (V:∀d,SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    (P:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)) (b:Presentation R.family)
    (portfolio:∀d,Mark.Portfolio R.family.params (V d) (W d))
    (issued:Hearthside R.family V W P b (Bandage.fly R.alloy.B.a))

include W portfolio issued
theorem original (d:ℕ) : ∃ radius:ℕ,∀ᶠ N:ℕ in atTop,
    ∀ (p:ℕ) (o:Site ((C).side N p)) (X:Config G ((C).side N p)→ℂ) (test:Continuous X)
      (_:LocalOn (Mark.Outer radius o) X) (x y:(C).label d),
    b.step d (N,p) x=b.step d (N,p) y →
    read R d N p o X test x-read R d N p o X test y=
      moment ((C).beta N p) (fun U=>residual C (V d) N p (P d (N,p)) (x-y) o U*X U):=by
  obtain ⟨radius,paid⟩:=WilsonThermometerReverseWard.single R V W P b portfolio issued d
  refine ⟨radius,?_⟩
  filter_upwards [paid] with N h
  intro p o X test away x y same
  have null:=h p (x-y) o X away (Mark.cont_envelope test)
  simp only [map_sub,same,sub_self,sub_zero] at null
  have h₀:=integrable R (((C).continuousO N p d (x-y) o).mul test)
  have h₁:=integrable R ((incoming_continuous (V d) N p (P d (N,p)) (x-y) o).mul test)
  rw [←map_sub]
  change moment ((C).beta N p) _=_
  simp only [WilsonOffsetReportingProducts.residual,Pi.sub_apply,sub_mul,moment]
  rw [integral_sub]
  rotate_left
  · exact h₀
  · exact h₁
  change _ = _ - moment ((C).beta N p) _
  rw [null,sub_zero]

end YM.Integration.WilsonThermometerWeakWardReading
end
