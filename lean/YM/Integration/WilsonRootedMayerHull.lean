import YM.RGLocalTaylor.Mayer.Moment
import YM.RGLocalTaylor.Laminate.Coincidence

/-! One original-period set of fine coordinates for a complete occupied Mayer component. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedMayerHull

open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open PhysicalNext PhysicalNext.Repeat Greenbelt Lotus Daisy RGLocalTaylor RGLocalTaylor.Mayer
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {W s μ C : ℝ} {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R} {j : ℕ}

/-- All the coordinates of the original Gaussian which the complete component can read. -/
abbrev coordinates (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F) :=
  podium S G (H.unionP p) X.B

/-- The same held Haar slice is used in both evaluations. A fitted insert depends jointly
on the fine coordinates from its genuine full shopping list. -/
theorem fitted {D : Support c} {r : Insert T} (h : Fits H r D j) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (y : F.Slice G) (v w : Air f G)
    (same : Pond.swim (podium S G D X.B) v=Pond.swim (podium S G D X.B) w) :
    r.joint X (y,v)=r.joint X (y,w) := by
  let X' := X.wrapY y
  have agree : Borough X' X' D v w ∅ ∅ R :=
    ⟨Village.refl X' D,fun i hi=>congrArg (fun a=>a (⟨i,hi⟩ : ↥(podium S G D X.B))) same,
      fun _ _=>Iff.rfl⟩
  exact h.regional X' X' hx hw D v w (Subset.refl _) agree

/-- Keep the whole original component, even before grading its regular exponentials. -/
theorem unexpanded (H : Cash W s μ L Q o C T R) (prior : Team R) (p : Molecule S)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (y : F.Slice G) (v : Air f G) :
    let E:=coordinates H p X
    let r:=Mayer.original H p (p\prior.signs S) (Laminate.partner prior H)
    r.joint X (y,v) = r.joint X (y,Pond.spill E (Pond.swim E v)) := by
  intro E r
  exact fitted (Laminate.fit_original (M:=prior) (H:=H) (j:=0) p) X hx hw y _ _ (Pond.settled E _).symm

/-- Every decorated grade has the identical complete hull, including every occupied marked and forced turn. -/
theorem decorated (H : Cash W s μ L Q o C T R) (prior : Team R) (p : Molecule S)
    {M : ℕ} (u : Decors (p\prior.signs S) M) (X : Coat T F)
    (hx : X.x=s) (hw : X.width=o.K) (y : F.Slice G) (v : Air f G) :
    let E:=coordinates H p X
    let r:=Mayer.tagged H p (Laminate.partner prior H) u
    r.joint X (y,v) = r.joint X (y,Pond.spill E (Pond.swim E v)) := by
  intro E r
  have hf (i : Head S) (hi : i∈p\(p\prior.signs S)) :
      Fits H (Laminate.partner prior H i) (H.supportP i) 0 := by
    have hs : i∈prior.signs S := by
      by_contra h
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hi).1,h⟩)
    exact (Laminate.partnerFit (H:=H) (j:=0) hs).1
  exact fitted (Mayer.fits_tagged H (Laminate.partner prior H) hf u) X hx hw y _ _ (Pond.settled E _).symm

end YM.Integration.WilsonRootedMayerHull
