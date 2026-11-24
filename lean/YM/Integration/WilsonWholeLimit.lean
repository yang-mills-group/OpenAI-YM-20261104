import YM.RGReadout.Grid.Quasi
import YM.Push.STRESS_FLUX.Matching
import YM.Integration.EngineeringWholeHorizon
import YM.Integration.PhysicalMSOPEInput

/-! Actual normalized Wilson products converge to the complete physical
moments on the same Final. The stronger separated statement applies the
existing Services receipt, which the common construction already retains.
The cutoff positions are the original ceil-rounded positions throughout. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonWholeLimit

open Function Filter Set MeasureTheory Extraction Table OPE OPE.Orbits Lattice
open scoped Classical Topology BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (H : Spec.Final C f S)
  {I J : Type} [Fintype I] [Fintype J] {d : I → ℕ} {e : J → ℕ}

/-- The complete product of the original physical representatives under
the original finite Wilson law; no perturbative replacement is made. -/
def product (x : I → E4) (v : Labels S d) (N p : ℕ) :
    Wilson.Config G (C.side N p) → ℂ := fun U =>
  ∏ i, C.seen (names v i) (StressFlux.Matching.ceilSite C N p (x i)) U

lemma product_continuous (x : I → E4) (v : Labels S d) (N p : ℕ) :
    Continuous (product x v N p) :=
  continuous_finsetProd _ fun i _ =>
    C.continuousO N p (d i) (S.representative _ (v i))
      (StressFlux.Matching.ceilSite C N p (x i))

lemma product_integrable (x : I → E4) (v : Labels S d) (N p : ℕ) :
    Integrable (product x v N p) (Wilson.law G (C.side N p) (C.beta N p)) :=
  Wilson.continuous_integrable (C.beta N p) (product_continuous x v N p)

lemma product_read (x : I → E4) (v : Labels S d) (N p : ℕ) :
    Wilson.moment (C.beta N p) (product x v N p) =
      (StressFlux.Matching.rounded C N p).read (points (x ∘ runNames I))
        (names v ∘ runNames I) := by
  apply congr_arg (Wilson.moment (C.beta N p))
  funext U
  exact (Equiv.prod_comp (runNames I)
    (fun i => C.seen (names v i) (StressFlux.Matching.ceilSite C N p (x i)) U)).symm

lemma product_split (x : I → E4) (v : Labels S d)
    (y : J → E4) (w : Labels S e) (N p : ℕ) (U : Wilson.Config G (C.side N p)) :
    product (beside x y) (stages v w) N p U =
      product x v N p U * product y w N p U := by
  unfold product
  exact Fintype.prod_sum_type _

include H in
/-- The generic-position limit needs only the retained Seed receipt. -/
theorem product_tendsto_generic (x : I → E4) (v : Labels S d)
    (hx : points (x ∘ runNames I) ∈ generic (Fintype.card I)) :
    Tendsto (fun z : ℕ × ℕ => Wilson.moment (C.beta z.1 z.2) (product x v z.1 z.2))
      f.fuse (𝓝 (Orbits.moment S x v)) := by
  rw [Orbits.observed, observe, worded, Table.readAt]
  apply (StressFlux.Matching.rounded_tendsto H.room.generic
    (names v ∘ runNames I) (points (x ∘ runNames I)) hx).congr'
  exact Eventually.of_forall fun (z : ℕ × ℕ) =>
    (product_read (C := C) (S := S) x v z.1 z.2).symm

include H in
/-- Services supplies the already proved uniform limit on compact
separated sets, including coordinate ties. This is applied to the same
ceil-rounded configurations, without a slice-genericity assertion. -/
theorem rounded_tendsto_separated (hS : Services C f S) {n : ℕ}
    (v : Fin n → C.book.Token) (x : Points n) (hx : x ∈ conf n) :
    Tendsto (fun z : ℕ × ℕ => (StressFlux.Matching.rounded C z.1 z.2).read x v)
      f.fuse (𝓝 (S.read x v)) := by
  let Y (z : ℕ × ℕ) := tag (C.S.a z.1) (address (C.S.a z.1) x)
  have hY : Tendsto Y f.fuse (𝓝 x) :=
    (chosen (S := C.S) x).comp (OPE.Cards.largeMesh f)
  obtain ⟨K, hK, hxK, hKc⟩ := exists_compact_subset (conf_open n) hx
  have hmem : ∀ᶠ z in f.fuse, Y z ∈ K :=
    hY.eventually (mem_interior_iff_mem_nhds.mp hxK)
  have hread : Tendsto (fun z => S.read (Y z) v) f.fuse (𝓝 (S.read x v)) :=
    (((S.smooth_read H.room.kernel.smooth v).continuousOn x hx).continuousAt
      ((conf_open n).mem_nhds hx)).tendsto.comp hY
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hbound : ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ a : Fin n → Lattice.Cover,
      tag (C.S.a z.1) a ∈ K →
      dist (lifted C z.1 z.2 v a) (S.read (tag (C.S.a z.1) a) v) < ε / 2 :=
    RGReadout.Literal.cornerLimit hS v K hK hKc (ε / 2) (half_pos hε)
  filter_upwards [hbound, hmem, Metric.tendsto_nhds.mp hread (ε / 2) (half_pos hε)]
    with z hb hz hr
  have hd : dist ((StressFlux.Matching.rounded C z.1 z.2).read x v)
      (S.read (Y z) v) < ε / 2 := hb (address (C.S.a z.1) x) hz
  exact (dist_triangle _ (S.read (Y z) v) _).trans_lt (by linarith)

include H in
theorem product_tendsto_separated (hS : Services C f S)
    (x : I → E4) (v : Labels S d) (hx : Injective x) :
    Tendsto (fun z : ℕ × ℕ => Wilson.moment (C.beta z.1 z.2) (product x v z.1 z.2))
      f.fuse (𝓝 (Orbits.moment S x v)) := by
  rw [Orbits.observed, observe, worded, Table.readAt]
  apply (rounded_tendsto_separated H hS (names v ∘ runNames I)
    (points (x ∘ runNames I)) (runs_conf.mpr hx)).congr'
  exact Eventually.of_forall fun (z : ℕ × ℕ) =>
    (product_read (C := C) (S := S) x v z.1 z.2).symm

include H in
theorem whole_tendsto_separated (hS : Services C f S)
    (x : I → E4) (v : Labels S d) (y : J → E4) (w : Labels S e)
    (hx : Injective (beside x y)) :
    Tendsto (fun z : ℕ × ℕ => Wilson.moment (C.beta z.1 z.2)
      (product (beside x y) (stages v w) z.1 z.2))
      f.fuse (𝓝 (whole S x v y w)) :=
  product_tendsto_separated H hS (beside x y) (stages v w) hx

include H in
/-- The running frame is fixed during both regulator limits, and is the
same frame on the finite product and on the complete continuum moment. -/
theorem whole_tendsto_actual (hS : Services C f S)
    (A : ℝ → PhysMS.tower S) (r : ℝ)
    (x : I → E4) (v : ∀ i, (Climb.Bel C.book).Field (d i))
    (y : J → E4) (w : Labels S e) (hx : Injective (beside x y)) :
    Tendsto (fun z : ℕ × ℕ => Wilson.moment (C.beta z.1 z.2)
      (product (beside x y) (stages (PhysMS.Frame.born A r v) w) z.1 z.2))
      f.fuse (𝓝 (whole S x (PhysMS.Frame.born A r v) y w)) :=
  whole_tendsto_separated H hS x (PhysMS.Frame.born A r v) y w hx

/-- Both terms are actual finite products under one normalized law. The
candidate insertion is at the original detector origin, with the identical
fixed exterior. This definition supplies no approximation estimate. -/
def detectorDiscrepancy (A : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (N p : ℕ) (i : Fin U.size) : Wilson.Config G (C.side N p) → ℂ :=
  product (beside x (OPE.positions S (U.listen i)).ofLp)
      (stages (PhysMS.Frame.born A r v) (fun j => (OPE.tags S (U.listen i) j).2)) N p -
    product (beside (sole (0 : E4)) (OPE.positions S (U.listen i)).ofLp)
      (stages (sole z : Labels S (fun _ : Unit => D))
        (fun j => (OPE.tags S (U.listen i) j).2)) N p

lemma detectorDiscrepancy_moment (A : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (N p : ℕ) (i : Fin U.size) :
    Wilson.moment (C.beta N p) (detectorDiscrepancy A U v r x z N p i) =
      Wilson.moment (C.beta N p)
        (product (beside x (OPE.positions S (U.listen i)).ofLp)
          (stages (PhysMS.Frame.born A r v) (fun j => (OPE.tags S (U.listen i) j).2)) N p) -
      Wilson.moment (C.beta N p)
        (product (beside (sole (0 : E4)) (OPE.positions S (U.listen i)).ofLp)
          (stages (sole z : Labels S (fun _ : Unit => D))
            (fun j => (OPE.tags S (U.listen i) j).2)) N p) := by
  exact integral_sub (product_integrable _ _ N p) (product_integrable _ _ N p)

include H in
theorem detectorDiscrepancy_tendsto (hS : Services C f S)
    (A : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (i : Fin U.size)
    (hx : Injective (beside x (OPE.positions S (U.listen i)).ofLp)) :
    Tendsto (fun q : ℕ × ℕ =>
      Wilson.moment (C.beta q.1 q.2) (detectorDiscrepancy A U v r x z q.1 q.2 i))
      f.fuse (𝓝 (PhysicalMSOPEReadout.candidateResidual A U v r x z i)) := by
  let E := U.listen i
  let y := (OPE.positions S E).ofLp
  let w : Labels S (fun j => (OPE.tags S E j).1) := fun j => (OPE.tags S E j).2
  have hi := whole_tendsto_actual H hS A r x v y w hx
  have he : Injective (beside (sole (0 : E4)) y) :=
    (consIn 0 y (e := Equiv.refl _)).mp (generic_conf _ (U.awake i))
  have ho := whole_tendsto_separated H hS (sole (0 : E4))
    (sole z : Labels S (fun _ : Unit => D)) y w he
  have hw : whole S (sole (0 : E4)) (sole z : Labels S (fun _ : Unit => D)) y w =
      witnessAt S D E z := (detector_witness_eq_upon H E (U.awake i) z).symm
  rw [hw] at ho
  exact (hi.sub ho).congr' (Eventually.of_forall fun q =>
    (detectorDiscrepancy_moment A U v r x z q.1 q.2 i).symm)

include H in
theorem detectorDiscrepancy_vector_tendsto (hS : Services C f S)
    (A : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D)
    (hx : ∀ i, Injective (beside x (OPE.positions S (U.listen i)).ofLp)) :
    Tendsto (fun q : ℕ × ℕ => fun i =>
      Wilson.moment (C.beta q.1 q.2) (detectorDiscrepancy A U v r x z q.1 q.2 i))
      f.fuse (𝓝 (PhysicalMSOPEReadout.candidateResidual A U v r x z)) :=
  tendsto_pi_nhds.mpr fun i => detectorDiscrepancy_tendsto H hS A U v r x z i (hx i)

include H in
theorem wholeReadout_discrepancy_tendsto (hS : Services C f S)
    (A : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D)
    (hx : ∀ i, Injective (beside x (OPE.positions S (U.listen i)).ofLp)) :
    Tendsto (fun q : ℕ × ℕ => EngineeringWeightedReadout.wholeReadout U A r
      (fun i => Wilson.moment (C.beta q.1 q.2)
        (detectorDiscrepancy A U v r x z q.1 q.2 i)))
      f.fuse (𝓝 (EngineeringWeightedReadout.wholeReadout U A r
        (PhysicalMSOPEReadout.candidateResidual A U v r x z))) :=
  (EngineeringWeightedReadout.wholeReadout U A r).continuous.continuousAt.tendsto.comp
    (detectorDiscrepancy_vector_tendsto H hS A U v r x z hx)

include H in
/-- Transport an actual finite-cutoff bound through the proved limit.
The finite estimate is not asserted here. -/
theorem wholeReadout_discrepancy_le (hS : Services C f S)
    (A : ℝ → PhysMS.tower S) {D : ℕ} (U : Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D)
    (hx : ∀ i, Injective (beside x (OPE.positions S (U.listen i)).ofLp)) (b : ℝ)
    (hb : ∀ᶠ q : ℕ × ℕ in f.fuse,
      ‖EngineeringWeightedReadout.wholeReadout U A r
        (fun i => Wilson.moment (C.beta q.1 q.2)
          (detectorDiscrepancy A U v r x z q.1 q.2 i))‖ ≤ b) :
    ‖EngineeringWeightedReadout.wholeReadout U A r
      (PhysicalMSOPEReadout.candidateResidual A U v r x z)‖ ≤ b :=
  le_of_tendsto (wholeReadout_discrepancy_tendsto H hS A U v r x z hx).norm hb

end YM.Integration.WilsonWholeLimit
