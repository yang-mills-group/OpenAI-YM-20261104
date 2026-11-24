import YM.Integration.ActualFoundryDetectorReadout
import YM.Integration.JointDetectorReadout

/-! The regional source is bound to the original finite physical detector,
including an empty internal product. One explicit actual unit pads the
internal index set; no detector field, exterior, or inverse column changes. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualFoundryDetectorSource
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Cells Extraction
open MergeProof MergeProof.Accent MergeProof.Replicum OPE.Therm OPE.Cards
open StressFlux.Matching WilsonMixedPlacement WilsonWholeLimit EngineeringWeightedReadout
open scoped Classical BigOperators Topology

variable {G : Gauge} {C : Family G} {S : Table C.book}
    {I : Type} [Fintype I] {d : I → ℕ} {D N p : ℕ}

def paddingSlots (I : Type) [Fintype I] : Fin (Fintype.card I + 1) ≃ Option I :=
  (Fintype.equivFinOfCardEq (by simp : Fintype.card (Option I) = Fintype.card I + 1)).symm

def paddedLabels (C : Family G) (unitDegree : ℕ) (v : I → C.book.Token)
    (j : Fin (Fintype.card I + 1)) : C.book.Token :=
  (paddingSlots I j).elim ⟨unitDegree, C.refUnit unitDegree⟩ v

def paddedPositions (x : I → E4) (j : Fin (Fintype.card I + 1)) : E4 :=
  (paddingSlots I j).elim 0 x

private theorem padding_product {M : Type*} [CommMonoid M] (g : I → M) :
    (∏ j, (paddingSlots I j).elim (1 : M) g) = ∏ i, g i := by
  calc
    _ = ∏ a : Option I, a.elim (1 : M) g :=
      (paddingSlots I).prod_comp (fun a : Option I => a.elim (1 : M) g)
    _ = _ := by
      rw [Fintype.prod_option]
      simp only [Option.elim_none, Option.elim_some, one_mul]

theorem padded_product (hC : C.Makes) (unitDegree : ℕ) (hUnit : C.ref unitDegree ≤ N)
    (v : I → C.book.Token) (x : I → E4) (U : Config G (C.side N p)) :
    (∏ j, C.O N p (paddedLabels C unitDegree v j).2
      (ceilSite C N p (paddedPositions x j)) U) =
      ∏ i, C.O N p (v i).2 (ceilSite C N p (x i)) U := by
  calc
    _ = ∏ j, (paddingSlots I j).elim (1 : ℂ)
        (fun i => C.O N p (v i).2 (ceilSite C N p (x i)) U) := by
      apply Finset.prod_congr rfl
      intro j _
      cases hj : paddingSlots I j with
      | none =>
        have hl : paddedLabels C unitDegree v j =
            ⟨unitDegree, C.refUnit unitDegree⟩ :=
          congrArg (fun q : Option I =>
            q.elim (⟨unitDegree, C.refUnit unitDegree⟩ : C.book.Token) v) hj
        have hx : paddedPositions x j = 0 :=
          congrArg (fun q : Option I => q.elim 0 x) hj
        exact (congrArg₂ (fun q : C.book.Token => fun y : E4 =>
          C.O N p q.2 (ceilSite C N p y) U) hl hx).trans
            (congrFun (C.constant hC unitDegree hUnit (ceilSite C N p 0)) U)
      | some i =>
        have hl : paddedLabels C unitDegree v j = v i :=
          congrArg (fun q : Option I =>
            q.elim (⟨unitDegree, C.refUnit unitDegree⟩ : C.book.Token) v) hj
        have hx : paddedPositions x j = x i :=
          congrArg (fun q : Option I => q.elim 0 x) hj
        exact congrArg₂ (fun q : C.book.Token => fun y : E4 =>
          C.O N p q.2 (ceilSite C N p y) U) hl hx
    _ = _ := padding_product _

def detectorCentral (A : ℝ → PhysMS.tower S)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (N p : ℕ) : Config G (C.side N p) → ℂ :=
  product x (PhysMS.Frame.born A r v) N p -
    product (OPE.sole (0 : E4))
      (OPE.sole z : OPE.Orbits.Labels S (fun _ : Unit => D)) N p

/-- Actual stencil footprints supply central locality independently of
the sharp signed estimate. Exterior fields are not included in this cell. -/
theorem central_interior (hC : C.Makes) (A : ℝ → PhysMS.tower S)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (K : Set (Site (C.side N p)))
    (hinner : ∀ j, (↑((C.localSection (d j)).footprint
      (ceilSite C N p (x j))) : Set (Site (C.side N p))) ⊆ K)
    (hcounter : (↑((C.localSection D).footprint
      (ceilSite C N p (0 : E4))) : Set (Site (C.side N p))) ⊆ K) :
    Interior K (detectorCentral A v r x z N p) := by
  have hi := JointSignedReadout.product_interior hC x (PhysMS.Frame.born A r v) K hinner
  have hz := JointSignedReadout.product_interior hC (OPE.sole (0 : E4))
    (OPE.sole z : OPE.Orbits.Labels S (fun _ : Unit => D)) K (fun _ => hcounter)
  convert hi.plus (hz.scale (-1)) using 1
  funext W
  simp only [detectorCentral, Pi.sub_apply, neg_one_mul, sub_eq_add_neg]

/-- The only analytic input here is the signed root bound itself. -/
theorem central_paid (hC : C.Makes) (A : ℝ → PhysMS.tower S)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) {Q : ℕ} (hQ : Q ≤ N) (a : ℝ)
    (hinner : ∀ j, (↑((C.localSection (d j)).footprint
      (ceilSite C N p (x j))) : Set (Site (C.side N p))) ⊆
        (center C.S p hQ 0).chamber 0)
    (hcounter : (↑((C.localSection D).footprint
      (ceilSite C N p (0 : E4))) : Set (Site (C.side N p))) ⊆
        (center C.S p hQ 0).chamber 0)
    (hsharp : (center C.S p hQ 0).rootTest (C.beta N p)
      (detectorCentral A v r x z N p) ≤ a) :
    PaidAt C.S N p Q (C.beta N p) a (detectorCentral A v r x z N p) :=
  ⟨hQ, central_interior hC A v r x z _ hinner hcounter, hsharp⟩

def detectorNumerator (A : ℝ → PhysMS.tower S) (U : OPE.Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (N p unitDegree zeroDegree : ℕ) (i : Fin U.size) :=
  numerator C N p
    (paddedLabels C unitDegree (OPE.Orbits.names (PhysMS.Frame.born A r v)))
    (OPE.detectorRaw S ⟨D, z⟩)
    (fun j => OPE.detectorRaw S (OPE.tags S (U.listen i) j))
    unitDegree zeroDegree (paddedPositions x) (OPE.positions S (U.listen i)).ofLp

theorem padded_central (hC : C.Makes) (unitDegree : ℕ) (hUnit : C.ref unitDegree ≤ N)
    (A : ℝ → PhysMS.tower S) (v : ∀ i, (Climb.Bel C.book).Field (d i))
    (r : ℝ) (x : I → E4) (z : S.Field D) :
    central N p (paddedLabels C unitDegree (OPE.Orbits.names (PhysMS.Frame.born A r v)))
      (OPE.detectorRaw S ⟨D, z⟩) (paddedPositions x) = detectorCentral A v r x z N p := by
  funext U
  rw [central, padded_product hC unitDegree hUnit]
  simp only [detectorCentral, Pi.sub_apply, product, Fintype.prod_unique]
  rfl

theorem physical_detector (hC : C.Makes) (unitDegree : ℕ) (hUnit : C.ref unitDegree ≤ N)
    (A : ℝ → PhysMS.tower S) (U : OPE.Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (i : Fin U.size) :
    physical C N p
        (paddedLabels C unitDegree (OPE.Orbits.names (PhysMS.Frame.born A r v)))
        (OPE.detectorRaw S ⟨D, z⟩)
        (fun j => OPE.detectorRaw S (OPE.tags S (U.listen i) j))
        (paddedPositions x) (OPE.positions S (U.listen i)).ofLp =
      detectorDiscrepancy A U v r x z N p i := by
  rw [JointSignedReadout.detectorDiscrepancy_factor]
  funext W
  change central N p _ _ _ W * _ = _
  rw [padded_central hC unitDegree hUnit]
  rfl

/-- The literal original detector, with all exterior factors, is the mean
of the same regional marked numerator at every actual readout level. -/
theorem normalized_detector (hC : C.Makes) (unitDegree zeroDegree : ℕ)
    (hUnit : C.ref unitDegree ≤ N) (A : ℝ → PhysMS.tower S) (U : OPE.Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (i : Fin U.size) {m : ℕ} (hm : m ≤ N) :
    (∫ W, (actualSignedTransport C (N := N)
        (detectorNumerator A U v r x z N p unitDegree zeroDegree i) hm W).part
        (Stock.final (Region (Fin (U.listen i).length))) ∂scene C.path N p m) =
      moment (C.beta N p) (detectorDiscrepancy A U v r x z N p i) := by
  rw [detectorNumerator, normalized_mean C hC N p _ _ _ unitDegree zeroDegree hUnit,
    physical_detector hC unitDegree hUnit]

/-- Each original detector row uses its own exterior cells and prices;
the central signed price is kept separate from those exterior costs. -/
theorem detector_row_bound (hC : C.Makes) (unitDegree : ℕ) (hUnit : C.ref unitDegree ≤ N)
    (A : ℝ → PhysMS.tower S) (U : OPE.Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (i : Fin U.size) {b q n Q t : ℕ}
    {hbq : b ≤ q} {hqn : q ≤ n}
    (P : PlacementAt C b q n hbq hqn (fun _ : Unit => 0)
      (OPE.positions S (U.listen i)).ofLp 1 t N p)
    (hqQ : q ≤ Q) (hQ : Q ≤ N) (a : ℝ) (B : Fin (U.listen i).length → ℝ)
    (hcentral : PaidAt C.S N p Q (C.beta N p) a (detectorCentral A v r x z N p))
    (hexterior : ∀ j, PaidAt C.S N p n (C.beta N p) (B j)
      (C.O N p (S.representative _ (OPE.tags S (U.listen i) j).2) 0)) :
    ‖moment (C.beta N p) (detectorDiscrepancy A U v r x z N p i)‖ ≤ a * ∏ j, B j := by
  rw [← physical_detector hC unitDegree hUnit A U v r x z i]
  apply mixed_bound hC _ P hqQ hQ _ _ _ _ a B
  · rwa [padded_central hC unitDegree hUnit]
  · exact hexterior

/-- The complete finite inverse keeps its original engineering columns.
No locality of the whole detector in the central cell is required. -/
theorem detector_readout_bound (hC : C.Makes) (unitDegree : ℕ)
    (hUnit : C.ref unitDegree ≤ N) (A : ℝ → PhysMS.tower S) (U : OPE.Detector S D)
    (v : ∀ i, (Climb.Bel C.book).Field (d i)) (r : ℝ) (x : I → E4)
    (z : S.Field D) (b q n Q t : Fin U.size → ℕ)
    (hbq : ∀ i, b i ≤ q i) (hqn : ∀ i, q i ≤ n i)
    (P : ∀ i, PlacementAt C (b i) (q i) (n i) (hbq i) (hqn i)
      (fun _ : Unit => 0) (OPE.positions S (U.listen i)).ofLp 1 (t i) N p)
    (hqQ : ∀ i, q i ≤ Q i) (hQ : ∀ i, Q i ≤ N)
    (a : Fin U.size → ℝ) (B : ∀ i, Fin (U.listen i).length → ℝ)
    (hcentral : ∀ i, PaidAt C.S N p (Q i) (C.beta N p) (a i)
      (detectorCentral A v r x z N p))
    (hexterior : ∀ i j, PaidAt C.S N p (n i) (C.beta N p) (B i j)
      (C.O N p (S.representative _ (OPE.tags S (U.listen i) j).2) 0)) :
    ‖wholeReadout U A r (fun i =>
      moment (C.beta N p) (detectorDiscrepancy A U v r x z N p i))‖ ≤
      columnPrice (wholeReadout U A r) (fun i => a i * ∏ j, B i j) := by
  apply column_bound
  intro i
  exact detector_row_bound hC unitDegree hUnit A U v r x z i
    (P i) (hqQ i) (hQ i) (a i) (B i) (hcentral i) (hexterior i)

private theorem detector_separated (U : OPE.Detector S D) (i : Fin U.size) :
    Injective (Sum.elim (fun _ : Unit => (0 : E4))
      (OPE.positions S (U.listen i)).ofLp) := by
  intro a b hab
  have h := U.awake i (0 : Axis)
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
    | inr b =>
      have he : (0 : Fin ((U.listen i).length + 1)) = b.succ :=
        h (show (Points.cons 0 (OPE.positions S (U.listen i))) 0 0 =
            (Points.cons 0 (OPE.positions S (U.listen i))) b.succ 0 from
          congrArg (fun z : E4 => z 0) hab)
      exact (Fin.succ_ne_zero b he.symm).elim
  | inr a =>
    cases b with
    | inl b =>
      have he : a.succ = (0 : Fin ((U.listen i).length + 1)) :=
        h (show (Points.cons 0 (OPE.positions S (U.listen i))) a.succ 0 =
            (Points.cons 0 (OPE.positions S (U.listen i))) 0 0 from
          congrArg (fun z : E4 => z 0) hab)
      exact (Fin.succ_ne_zero a he).elim
    | inr b =>
      apply congrArg Sum.inr
      apply Fin.succ_injective
      exact h (show (Points.cons 0 (OPE.positions S (U.listen i))) a.succ 0 =
          (Points.cons 0 (OPE.positions S (U.listen i))) b.succ 0 from
        congrArg (fun z : E4 => z 0) hab)

/-- The actual complete detector gets its exterior prices, separation,
and mixed-cell placement from the same retained Final. Central locality is
proved from the original full footprints; the sharp signed root bound is
the separate analytic input. Its Q may grow after the exterior levels and
all readout column costs have been fixed. -/
theorem complete_detector_readout {f : Extraction.Order}
    (F : Spec.Final C f S) (U : OPE.Detector S D) (δ : ℝ) (hδ : 0 < δ)
    (bufferMin : ℕ) :
    ∃ q n : Fin U.size → ℕ,
      ∃ B : (i : Fin U.size) → Fin (U.listen i).length → ℝ,
        (∀ i, bufferMin ≤ q i ∧ q i ≤ n i) ∧
        ∀ᶠ w : ℕ × ℕ in f.fuse,
          ∀ Q : Fin U.size → ℕ, (∀ i, q i ≤ Q i) → ∀ hQN : ∀ i, Q i ≤ w.1,
          ∀ (A : ℝ → PhysMS.tower S)
            (v : ∀ i, (Climb.Bel C.book).Field (d i))
            (r : ℝ) (x : I → E4) (z : S.Field D) (a : Fin U.size → ℝ),
          (∀ i j, (↑((C.localSection (d j)).footprint
              (ceilSite C w.1 w.2 (x j))) : Set (Site (C.side w.1 w.2))) ⊆
            (center C.S w.2 (hQN i) 0).chamber 0) →
          (∀ i, (↑((C.localSection D).footprint
              (ceilSite C w.1 w.2 (0 : E4))) : Set (Site (C.side w.1 w.2))) ⊆
            (center C.S w.2 (hQN i) 0).chamber 0) →
          (∀ i, (center C.S w.2 (hQN i) 0).rootTest (C.beta w.1 w.2)
            (detectorCentral A v r x z w.1 w.2) ≤ a i) →
          ‖wholeReadout U A r (fun i =>
            moment (C.beta w.1 w.2) (detectorDiscrepancy A U v r x z w.1 w.2 i))‖ ≤
            columnPrice (wholeReadout U A r) (fun i => a i *
              ∏ j, (B i j * C.S.a (n i) ^
                (-((OPE.tags S (U.listen i) j).1 : ℝ) - δ) + 1)) := by
  let dE (i : Fin U.size) (j : Fin (U.listen i).length) :=
    (OPE.tags S (U.listen i) j).1
  let e (i : Fin U.size) (j : Fin (U.listen i).length) : C.label (dE i j) :=
    S.representative _ (OPE.tags S (U.listen i) j).2
  let R (i : Fin U.size) (j : Fin (U.listen i).length) : ℝ := 1 + ‖e i j‖
  have hR (i : Fin U.size) (j : Fin (U.listen i).length) : 0 < R i j :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  choose b hb q hq n hqn B hB H using fun i : Fin U.size =>
    complete_readout (arity := Fintype.card I) F (dE i) (R i) (hR i) δ hδ
      (OPE.positions S (U.listen i)).ofLp (detector_separated U i) 0 bufferMin
  refine ⟨q, n, B, fun i => ⟨(le_max_right (b i) bufferMin).trans (hq i), hqn i⟩, ?_⟩
  have hUnit : ∀ᶠ w : ℕ × ℕ in f.fuse, C.ref 0 ≤ w.1 := by
    rw [Order.fused, Order.late]
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop (C.ref 0)
  filter_upwards [eventually_all.mpr H, hUnit] with w hw hunit
  intro Q hQ hQN A v r x z a hinner hcounter hsharp
  have hcentral (i : Fin U.size) := central_paid F.room.cutoff A v r x z (hQN i)
    (a i) (hinner i) (hcounter i) (hsharp i)
  apply column_bound
  intro i
  have he (j : Fin (U.listen i).length) : ‖e i j‖ ≤ R i j :=
    le_add_of_nonneg_left zero_le_one
  have hc : PaidAt C.S w.1 w.2 (Q i) (C.beta w.1 w.2) (a i)
      (central w.1 w.2
        (paddedLabels C 0 (OPE.Orbits.names (PhysMS.Frame.born A r v)))
        (OPE.detectorRaw S ⟨D, z⟩) (paddedPositions x)) := by
    rw [padded_central F.room.cutoff 0 hunit]
    exact hcentral i
  have h := hw i (Q i) (hQ i) (hcentral i).live (e i) he
    (paddedLabels C 0 (OPE.Orbits.names (PhysMS.Frame.born A r v)))
    (OPE.detectorRaw S ⟨D, z⟩) (paddedPositions x) (a i) hc 0 0 hunit w.1 le_rfl
  change ‖∫ W, (actualSignedTransport C (N := w.1)
      (detectorNumerator A U v r x z w.1 w.2 0 0 i) le_rfl W).part
      (Stock.final (Region (Fin (U.listen i).length))) ∂scene C.path w.1 w.2 w.1‖ ≤ _ at h
  rw [normalized_detector F.room.cutoff 0 0 hunit] at h
  exact h

end YM.Integration.ActualFoundryDetectorSource
