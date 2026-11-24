import YM.Integration.WilsonRootedMayerOriginal

/-! The protected local tag payroll and the exact untouched remainder of the original likelihood. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedMayerTagLaw

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Lotus Daisy RGLocalTaylor RGLocalTaylor.Mayer
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {P : Teller G} {R : Rep G f} {W s μ C : ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

def protectedSites (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F) (z : Air f G) : Support c :=
  (H.unionP p).filter fun i=>¬Inside i X.seeds (30*X.B) ∧ X.watch i o.ξ R.beta X.B z

def protectedBonds (E : Support c) : Finset (Bond c) := univ.filter fun e=>e.1∈E

/-- Every original tag factor outside these certified posting sites remains field-dependent. -/
def remaining (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F) (z : Air f G) : ℝ :=
  let U:=X.input (X.liftA R.beta z)
  let I:=protectedSites H p X z
  (∏ i∈univ\I,Tags.siteMass U X.k i)*(∏ e∈univ\protectedBonds I,Tags.pinMass U X.k e)

private theorem erase {ι : Type} [Fintype ι] [DecidableEq ι] (I : Finset ι) (a : ι→ℝ)
    (one : ∀ i∈I,a i=1) : (∏ i,a i) = ∏ i∈univ\I,a i := by
  have h:=Finset.prod_sdiff (f:=a) (subset_univ I)
  rw [Finset.prod_eq_one one,mul_one] at h
  exact h.symm

/-- Protected site and bond factors are individually one. This holds for the real
incoming action and the original affine field on the held forest and tag. -/
theorem certified (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest) (stamp : Stamp T) (z : Air f G) :
    let U:=X.input (X.liftA R.beta z)
    let I:=protectedSites H p X z
    (∀ i∈I, Tags.siteMass U X.k i=1) ∧
      (∀ e∈protectedBonds I,Tags.pinMass U X.k e=1) := by
  intro U I
  have safety:=((H.laws.data.safety.2.2.2 F X hx hw hm).2 stamp)
  have here (i : Site c) (hi : i∈I) := safety i (mem_filter.mp hi).2.1 R.beta
    H.laws.intake.positive z (mem_filter.mp hi).2.2
  exact ⟨fun i hi=>(here i hi).1,fun e he=>((here e.1 (mem_filter.mp he).2).2.2 e.2).1⟩

/-- The uniformly enumerated tags, with precisely the remaining likelihood factors in
their integrand, equal the genuine field-dependent physical likelihood before summing. -/
theorem original (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest) (stamp : Stamp T) (z : Air f G) :
    S.likelihood (X.input (X.liftA R.beta z)) X.k =
      (Fintype.card S.Choices:ℝ)⁻¹ * remaining H p X z := by
  obtain ⟨hf,he⟩:=certified H p X hx hw hm stamp z
  exact (Tags.likelihood_all _ _).trans (congr_arg (_*·) (congr_arg₂ (·*·) (erase _ _ hf) (erase _ _ he)))

/-- Retain the entire physical forced contract and fine/coarse partition of one
ungraded original sector even when other sites or edges miss their protected branch. -/
theorem storm (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest) (stamp : Stamp T) (z : Air f G) (k : Finset ℕ) :
    let v:=X.liftA R.beta z
    let U:=X.input v
    (Fintype.card S.Choices:ℝ)⁻¹*(∏ i : Panic c f,X.rawStorm v W X.seeds R k i) =
      X.χ.distribute X.seeds X.x W U X.k X.V *
        ((Fintype.card S.Choices:ℝ)⁻¹ * remaining H p X z) * Contract.order R k univ U := by
  intro v U
  exact (X.distributions v W k R hm).trans
    (congr_arg (fun a=>X.χ.distribute X.seeds X.x W U X.k X.V * a * Contract.order R k univ U)
      (original H p X hx hw hm stamp z))

end YM.Integration.WilsonRootedMayerTagLaw
