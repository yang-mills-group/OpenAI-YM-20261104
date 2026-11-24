import YM.Integration.JointSignedReadout
import YM.Integration.WilsonWholeLimit

/-! The signed readout applied to the original finite physical products.

The exterior product is retained exactly. Locality of the internal
discrepancy alone is not asserted to imply locality of this whole product.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.JointSignedReadout
open Function Lattice Wilson RG Cells Extraction Table OPE
open EngineeringWeightedReadout WilsonWholeLimit
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {S : Table C.book}
    {I : Type} [Fintype I] {d : I → ℕ} {D N p : ℕ}

/-- Actual gauge invariance, continuity and stencil locality give locality
of the whole physical product once every translated footprint fits. -/
theorem product_interior (hC : C.Makes) (x : I → E4)
    (v : OPE.Orbits.Labels S d) (K : Set (Site (C.side N p)))
    (hfit : ∀ i, (↑((C.localSection (d i)).footprint
      (StressFlux.Matching.ceilSite C N p (x i))) : Set (Site (C.side N p))) ⊆ K) :
    Interior K (product x v N p) := by
  unfold product
  apply Interior.combines _ Finset.univ
  intro i _
  have he := C.continuousO N p (d i) (S.representative _ (v i))
    (StressFlux.Matching.ceilSite C N p (x i))
  refine ⟨C.invariant hC _ _ _ _ _, he.measurable, ?_,
    he.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
  intro U W hUW
  exact C.localO N p (d i) (S.representative _ (v i)) _ U W
    (agrees_mono hUW (hfit i))

/-- The same exterior multiplies both terms, under the same finite law.
This is a pointwise identity, without any independence assertion. -/
theorem detectorDiscrepancy_factor (A : ℝ → PhysMS.tower S) (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (i : Fin U.size) :
    detectorDiscrepancy A U v r x z N p i =
      (product x (PhysMS.Frame.born A r v) N p -
        product (sole (0 : E4)) (sole z : OPE.Orbits.Labels S (fun _ : Unit => D)) N p) *
      product (OPE.positions S (U.listen i)).ofLp
        (fun j => (OPE.tags S (U.listen i) j).2) N p := by
  funext W
  simp only [detectorDiscrepancy, Pi.sub_apply, Pi.mul_apply,
    product_split, sub_mul]

/-- The footprint obligation includes the exterior labels explicitly.
The field values are arbitrary; only their actual grades enter the fit. -/
theorem detectorDiscrepancy_interior (hC : C.Makes)
    (A : ℝ → PhysMS.tower S) (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (i : Fin U.size) (K : Set (Site (C.side N p)))
    (hinner : ∀ j, (↑((C.localSection (d j)).footprint
      (StressFlux.Matching.ceilSite C N p (x j))) : Set (Site (C.side N p))) ⊆ K)
    (hcandidate : (↑((C.localSection D).footprint
      (StressFlux.Matching.ceilSite C N p (0 : E4))) : Set (Site (C.side N p))) ⊆ K)
    (hexterior : ∀ j, (↑((C.localSection (OPE.tags S (U.listen i) j).1).footprint
      (StressFlux.Matching.ceilSite C N p ((OPE.positions S (U.listen i)).ofLp j))) :
        Set (Site (C.side N p))) ⊆ K) :
    Interior K (detectorDiscrepancy A U v r x z N p i) := by
  rw [detectorDiscrepancy_factor]
  have hi := product_interior hC x (PhysMS.Frame.born A r v) K hinner
  have hz := product_interior hC (sole (0 : E4))
    (sole z : OPE.Orbits.Labels S (fun _ : Unit => D)) K (fun _ => hcandidate)
  have he := product_interior hC (OPE.positions S (U.listen i)).ofLp
    (fun j => (OPE.tags S (U.listen i) j).2) K hexterior
  convert (hi.plus (hz.scale (-1))).times he using 1
  funext W
  simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg, neg_one_mul]

/-- Native reflection positivity controls the literal complete physical
discrepancy. The original inverse-frame column prices and whole-product
cell locality remain explicit. -/
theorem detectorDiscrepancy_readout (hC : C.Makes)
    (A : ℝ → PhysMS.tower S) (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (T : Fin U.size → Tiling (C.side N p))
    (hF : ∀ i, Interior ((T i).chamber 0)
      (detectorDiscrepancy A U v r x z N p i)) :
    ‖wholeReadout U A r (fun i =>
      moment (C.beta N p) (detectorDiscrepancy A U v r x z N p i))‖ ≤
      columnPrice (wholeReadout U A r) (fun i =>
        (T i).rootTest (C.beta N p) (detectorDiscrepancy A U v r x z N p i)) :=
  wholeReadout_signed_actual hC U A r T
    (detectorDiscrepancy A U v r x z N p) hF

end YM.Integration.JointSignedReadout
