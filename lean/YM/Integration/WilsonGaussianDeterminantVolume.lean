import YM.Integration.WilsonGaussianDeterminantPhysical

/-! Complete finite-volume half-log determinant and its no-hole model on the same marked conditional field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantVolume

open LocalTaylorR2 LocalTaylorR2.Pavilion Analysis
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Axial Channel Canvas Mesh Port Work.G05 Animals Itinerary Reserves Census

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
variable {F : Forest S.ratio} {P : Teller G}

open PhysicalAffineScalarLogarithm
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {F : Forest S.ratio} {R : Rep G f} {W s μ C : ℝ} {P : Teller G}
  {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W}

open WilsonGaussianDeterminantFull WilsonGaussianDeterminantVertex
open RGLocalTaylor LocalLTE.Fan
open WilsonGaussianDeterminantRoster (model)

def scalar (X : Coat T F) := (Real.log X.blank.plate.det-Real.log X.plate.det)/2

theorem original (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)
    (L : Side) (D : Patch) (hD : D.Branches P.bind G) (χ : Chi) (p j : ℕ)
    (v d : ℝ → ℝ) (hv : Rate G L (-(1/2)) v) (hu : ∀ᶠ s : ℝ in atTop, 0 ≤ v s)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R), S.patch = D →
      Sees H j (v s) (d s) χ (fun _ X _ => scalar X - ∑ i, (seed X i + model p R X i))
        ((Fintype.card (Bond f):ℝ)*(ε*(gStep R.beta)^p)) 1 := by
  have paid := WilsonGaussianDeterminantPhysical.original P Q o L D hD χ p j v d hv hu ε hε
  have charts := Glass.portal P D L hD j χ hv hu o.K o.γ W o.indexPay o.f
  filter_upwards [paid,charts] with s paid charts
  intro c f S T R μ C H hS E _ _ _ F X V u z x w hx hk hm hχ hV hC
  let g (i : Bond f) (y:E) := let Y:=vary X (V y); fullPair Y i - seed Y i - model p R Y i
  have hsum := Brush.spree (univ : Finset (Bond f)) g (fun _ => ε*(gStep R.beta)^p)
    zero_le_one (fun i _ => paid c f S T R μ C H i hS E F X V u z x w hx hk hm hχ hV hC)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  apply hsum.shimmy
  have port := H.laws.data.localP F X hx hk hm
  have glass := charts c f S T hS H.laws.data.funds H.laws.data.access F X hk hχ hx port E V x hC.atV hV
  filter_upwards [WilsonGaussianDeterminantGerm.logged X glass port] with y hy
  let Y := vary X (V y)
  change scalar Y - ∑ i, (seed Y i + model p R Y i) = ∑ i, (fullPair Y i-seed Y i-model p R Y i)
  change (∑ i,fullPair Y i) = scalar Y at hy
  rw [← hy,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  ring

theorem empty_seed (X : Coat T F) (h : X.seeds.place = ∅) (i : Bond f) : seed X i = 0 := by
  have cleared : X.seeds.dome (200*X.B) = ∅ := by simp [Stores.dome,h,Lattice.halo]
  simp [seed,voyage,cleared]

theorem seedless (p : ℕ) (R : Rep G f) (X : Coat T F) (clean : X.seeds.place = ∅) :
    (∑ i, (seed X i + model p R X i)) = ∑ i, model p R X i := by
  exact Finset.sum_congr rfl fun i _ => (congrArg (·+model p R X i) (empty_seed X clean i)).trans (zero_add _)

theorem unpunctured {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
    (V : E → Config G c) (p j : ℕ) (R : Rep G f) (X : Coat T F) (clean : X.seeds.place = ∅)
    (C : ℝ) (paid : Brush j C 1 (fun y => let Y:=vary X (V y)
      scalar Y - ∑ i, (seed Y i + model p R Y i)) x) :
    Brush j C 1 (fun y => let Y:=vary X (V y); scalar Y - ∑ i, model p R Y i) x := by
  apply paid.shimmy
  filter_upwards with y
  let Y := vary X (V y)
  exact congrArg (scalar Y - ·) (seedless p R Y clean).symm

end YM.Integration.WilsonGaussianDeterminantVolume
end
