import YM.Integration.WilsonGaussianDeterminantMarked

/-! The cutoff resolvent and the complete matrix trace agree up to the paid finite-window term on a neighborhood of each actual marked germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantGerm

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

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
variable {V : E → Config G c} {j : ℕ} {Y a b e ρ : ℝ}

theorem nonsingular (X : Coat T F) (h : Glass P X V x j Y)
    (p : Rotator P L e a b ρ X) :
    ∀ᶠ y in 𝓝 x, ∀ t ∈ Set.uIcc (0:ℝ) 1, IsUnit (glide (vary X (V y)).plate t).det := by
  let I := Set.uIcc (0:ℝ) 1
  let A y := (vary X (V y)).plate
  have ha : ContinuousAt A x :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun k => (h.vest i k).continuousAt
  have h₀ : A x = X.plate := by unfold A; rw [h.lifts]; rfl
  let K (z : E × ℝ) := (glide (A z.1) z.2).det
  let U := {z | IsUnit (K z)}
  have interior_at (t : ℝ) (ht : t ∈ I) : (x,t) ∈ interior U := by
    have hm : ContinuousAt (uncurry fun y t => glide (A y) t) (x,t) :=
      continuousAt_const.add (continuous_snd.continuousAt.smul
        ((show ContinuousAt (A ∘ Prod.fst) (x,t) from ContinuousAt.comp ha continuousAt_fst).sub continuousAt_const))
    have detC : Continuous (fun M : Mat f G => M.det) := continuous_id.matrix_det
    have hk : ContinuousAt K (x,t) := detC.continuousAt.comp hm
    have nonzero : IsUnit (K (x,t)) := by
      unfold K
      rw [h₀]
      exact Matrix.isUnit_det_of_right_inverse
        ((p.scale.glide p.full.hv p.full.hQ t (Set.uIcc_of_le (zero_le_one (α:=ℝ)) ▸ ht)).initial.1)
    exact mem_interior_iff_mem_nhds.mpr ((hk.eventually_ne nonzero.ne_zero).mono
      (fun z hz => isUnit_iff_ne_zero.mpr hz))
  obtain ⟨u,v,hu,-,hx,hI,hprod⟩ := generalized_tube_lemma (isCompact_singleton (x:=x))
    (show IsCompact I from isCompact_uIcc) (isOpen_interior (s:=U))
    (show Set.prod {x} I ⊆ interior U from by
      rintro ⟨y,t⟩ ⟨hy,ht⟩
      have hy : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact interior_at t ht)
  filter_upwards [hu.mem_nhds (hx (Set.mem_singleton x))] with y hy t ht
  exact (show (y,t) ∈ U from interior_subset (hprod (show (y,t) ∈ u.prod v from ⟨hy,hI ht⟩)))

private theorem split {B : ℕ} (D : Window (along (G:=G) S) B) (A : Mat f G) (i : Bond f)
    (restricted : ContinuousOn (fun t => D.pad (glide A t)) (Set.uIcc (0:ℝ) 1))
    (complete : ContinuousOn (fun t => (glide A t)⁻¹) (Set.uIcc (0:ℝ) 1)) :
    windowDifference D A i = Batch.joint A D i - full A i := by
  unfold windowDifference Batch.joint full
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h₁ : ContinuousOn (fun t => (A-1)*D.pad (glide A t)) (Set.uIcc (0:ℝ) 1) :=
    continuousOn_const.mul restricted
  have h₂ : ContinuousOn (fun t => (A-1)*(glide A t)⁻¹) (Set.uIcc (0:ℝ) 1) :=
    continuousOn_const.mul complete
  simp only [localBase,lact,intensity,pow_zero,mul_one,Pulse.coil,mul_sub,Matrix.sub_apply]
  exact intervalIntegral.integral_sub
    (continuousOn_pi.mp (continuousOn_pi.mp h₁ (i,k)) (i,k)).intervalIntegrable
    (continuousOn_pi.mp (continuousOn_pi.mp h₂ (i,k)) (i,k)).intervalIntegrable

theorem rooted (X : Coat T F) (h : Glass P X V x j Y) (port : Port P L e a b ρ X) (i : Bond f) :
    ∀ᶠ y in 𝓝 x, let Z := vary X (V y)
      Z.undercurrent i + seed Z i - fullPair Z i = correction Z i := by
  have flat := difference_eq X.shutter X.blank.plate port.sails.full port.empty.scale i
  filter_upwards [Stained.eventual_hue h port.sails,nonsingular X h port.sails] with y h₁ h₂
  let Z := vary X (V y)
  have curved := split X.shutter Z.plate i h₁ (flowing _ (strung Z.plate) h₂)
  have marked : Z.undercurrent i + seed Z i = Z.condensation i := by
    by_cases h : voyage Z.seeds (200*Z.B) i <;> simp [Coat.undercurrent,seed,h]
  change Z.undercurrent i + seed Z i - fullPair Z i = correction Z i
  rw [marked]
  change (Batch.joint X.blank.plate X.shutter i-Batch.joint Z.plate X.shutter i)/2 -
    (full X.blank.plate i-full Z.plate i)/2 =
    (windowDifference X.shutter X.blank.plate i-windowDifference X.shutter Z.plate i)/2
  rw [flat,curved]
  ring

private theorem sum_at (A : Mat f G)
    (ha : ∀ t ∈ Set.uIcc (0:ℝ) 1, IsUnit (glide A t).det) :
    (∑ i, full A i) = Real.log A.det := by
  have h : Real.log A.det = ∑ k, Pulse.coil A k := by
    have ht : ContinuousOn (fun t => (A-1)*(glide A t)⁻¹) (Set.uIcc (0:ℝ) 1) :=
      continuousOn_const.mul (flowing _ (strung A) ha)
    have invert t (ht : t ∈ Set.Icc (0:ℝ) 1) := ha t ((Set.uIcc_of_le (zero_le_one (α:=ℝ))) ▸ ht)
    rw [Pulse.total A invert]
    unfold Pulse.coil
    exact intervalIntegral.integral_finsetSum (f:=fun k t => ((A-1)*(glide A t)⁻¹) k k)
      fun k _ => (continuousOn_pi.mp (continuousOn_pi.mp ht k) k).intervalIntegrable
  simpa only [full,Fintype.sum_prod_type] using h.symm

theorem logged (X : Coat T F) (h : Glass P X V x j Y) (port : Port P L e a b ρ X) :
    ∀ᶠ y in 𝓝 x, let Z := vary X (V y)
      (∑ i, fullPair Z i) = (Real.log Z.blank.plate.det - Real.log Z.plate.det)/2 := by
  have flat := sum_full X.blank.plate port.sails.full port.empty.scale
  filter_upwards [nonsingular X h port.sails] with y real
  change (∑ i, fullPair (vary X (V y)) i) = _
  unfold fullPair
  rw [← Finset.sum_div,Finset.sum_sub_distrib,sum_at _ real]
  change ((∑ i, full X.blank.plate i)-Real.log (vary X (V y)).plate.det)/2 = _
  rw [flat]
  rfl

end YM.Integration.WilsonGaussianDeterminantGerm
end
