import YM.Integration.WilsonMarkedProducts
import YM.FormalOPE.RG10.MultiGauge.Engineered

/-! Feed the existing actual Wilson insertion dictionary into the finite
inversion-regulated Schur supplier. The source Family, calibration, engineering
factor and coefficient convention remain fixed. This is a finite-regulator
identity; it does not assert volume-uniform IR removal or identify the regulated
measure with the physical Family's measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG Source PowerSeries
open RG06 RG06.WilsonCompiler PertExtension PertExtension.Orb
open PertExtension.Chart PertExtension.Series PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.StationaryMarks
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

/-- Polynomial source sections are smooth on the actual inversion tree chart. -/
theorem section_inversion_smooth (Q : SectionData F) (v : F.Coeff) (o : Site n) :
    ContDiff ℝ ∞ (fun A : Orb.Dir G n => Q.places v o (Orb.representative A)) := by
  let b i (A : Orb.Dir G n) := Source.entry (S := Q.stencil)
    (expandAt o (Orb.representative A)) i
  have hb i : ContDiff ℝ ∞ (b i) := by
    let j := i.2.1
    let k := i.2.2.1
    let L : G.Mat →L[ℝ] ℂ :=
      ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin G.repDim => ℂ) k).comp
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin G.repDim => Fin G.repDim → ℂ) j)).toContinuousLinearMap
    have hh := L.contDiff.comp (Orb.matrix_smooth (G := G) (wrap n i.1.val.1 + o, i.1.val.2))
    unfold b Source.entry
    cases i.2.2.2
    · exact hh.of_le le_top
    exact ((starL ℝ (A := ℂ)).contDiff.comp hh).of_le le_top
  let φ (p : MvPolynomial (Source.Index G Q.stencil) ℂ) (A : Orb.Dir G n) :=
    MvPolynomial.aeval (fun i => b i A) p
  have hs p : ContDiff ℝ ∞ (φ p) := by
    induction p using MvPolynomial.induction_on with
    | C a => unfold φ; simp only [MvPolynomial.aeval_C]; exact contDiff_const
    | add p q hp hq => unfold φ; simp only [map_add]; exact hp.add hq
    | mul_X p i hp => unfold φ; simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (hb i)
  exact hs (Q.evalC v)

variable (C : Family G) (N p d : ℕ)

def physicalInversionObservable (x : Site (C.side N p))
    (i : (C.labels.level d).Index) (U : Config G (C.side N p)) : ℝ :=
  (C.O N p (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)) x U).re

theorem actual_inversion_smooth (v : C.label d) (x : Site (C.side N p)) :
    ContDiff ℝ ∞ (fun A : Orb.Dir G (C.side N p) => C.O N p v x (Orb.representative A)) := by
  simp_rw [Dict06.Actual.names]
  exact contDiff_const.mul (section_inversion_smooth (C.localSection d)
    (Dict06.Actual.matrix C N p d v) x)

theorem physicalInversion_pretest (hC : C.Makes) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) :
    Orb.PreTest (physicalInversionObservable C N p d x i) := by
  have hc : Continuous (physicalInversionObservable C N p d x i) :=
    Complex.continuous_re.comp (C.continuousO N p d _ x)
  refine ⟨fun g _ U => congrArg Complex.re (C.invariant hC N p d _ x g U),
    ⟨hc.comp Orb.continuous_links, ?_⟩, hc⟩
  exact (Complex.reCLM.contDiff.comp (actual_inversion_smooth C N p d _ x)).contDiffAt

theorem physicalInversion_real (hC : C.Makes) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) (U : Config G (C.side N p)) :
    (physicalInversionObservable C N p d x i U : ℂ) =
      C.O N p (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)) x U := by
  apply Complex.conj_eq_iff_re.mp
  rw [Dict06.Actual.names, Dict06.Actual.meet, (C.labels.level d).coords_basis]
  have hs : star (Pi.single i (1 : ℂ) : C.label d) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply]
  change star (_ * _) = _
  rw [star_mul, ← (hC.sections d).ordinary_real, hs, mul_comm]
  congr 1
  simp [Dict06.Actual.factor]

/-- The signed extension of cotree coordinates is exactly the exponential
chart used by the physical positive-link dictionary. -/
theorem inversion_chart_roll (t : ℝ) (u : Orb.Dir G n) :
    Orb.links (K := G.El) 1 (expLinks G _ (t • u)) = roll (Orb.variation u) t := by
  funext e
  unfold Orb.links Orb.liftLinks Orb.splitLink roll Orb.variation Orb.genJet
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, expLinks, Pi.one_apply]
  split_ifs
  all_goals first | exact rfl | (simp; done) | simp only [smul_neg, Work.F03.exp_neg_color]

/-- The IR consumer coordinates are the exact signed cotree extension,
expressed through its existing coordinate equivalence. -/
def wilsonInversionCoordinates (u : Orb.Dir G (C.side N p)) :
    RG09.Graph.Tor (RG09.Walls.Spin G) (C.side N p) → ℝ :=
  access G (Orb.variation u) ∘ (RG09.Walls.assign G).symm

/-- The latest inversion-top raw kernel reads precisely the already identified
actual Wilson film, with ordinary factorial coefficients. -/
theorem physicalInversion_raw (hC : C.Makes) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) (u : Orb.Dir G (C.side N p)) :
    InversionTop.raw (Orb.restrictedO (physicalInversionObservable C N p d x i)) ((),u) =
      develop (access G (Orb.variation u)) (physicalFilm C N p d x
        (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) := by
  let f : Orb.Dir G (C.side N p) → ℝ :=
    Orb.restrictedO (physicalInversionObservable C N p d x i) ∘ expLinks G _
  have hf : ContDiffAt ℝ ∞ f 0 := (physicalInversion_pretest C N p d hC x i).curved.germ
  have hr : ContDiffAt ℝ ∞ (fun t : ℝ => f (t • u)) 0 := by
    let g : ℝ → Orb.Dir G (C.side N p) := fun t => t • u
    change ContDiffAt ℝ ∞ (f ∘ g) 0
    apply ContDiffAt.comp _ (g := f) (f := g) ?_ (contDiffAt_id.smul contDiffAt_const)
    rw [show g 0 = 0 by simp [g]]
    exact hf
  ext1 k
  rw [InversionTop.raw, InversionTop.lift, InversionTop.into_coeff, PowerSeries.coeff_mk]
  change (jet f k u : ℂ) = _
  rw [develop_coeff, physicalFilm_coefficient]
  rw [homogeneous_derivative f u k (hf.of_le (WithTop.coe_le_coe.mpr le_top))]
  change ((Dict06.Series.ordinary k (fun t : ℝ => f (t • u)) : ℝ) : ℂ) = _
  change Complex.ofRealCLM (Dict06.Series.ordinary k (fun t : ℝ => f (t • u))) = _
  rw [← Dict06.Series.ordinary_map (fun t : ℝ => f (t • u)) k
    (hr.of_le (WithTop.coe_le_coe.mpr le_top)) Complex.ofRealCLM]
  apply congrArg (Dict06.Series.ordinary k)
  funext t
  change (physicalInversionObservable C N p d x i (Orb.links 1 (expLinks G _ (t • u))) : ℂ) = _
  rw [physicalInversion_real C N p d hC, inversion_chart_roll]

/-- Exact equality with RG09's already constructed real source coefficients. -/
theorem wilsonInversion_raw_source (hC : C.Makes) (x : Site (C.side N p))
    (i : (C.labels.level d).Index) (u : Orb.Dir G (C.side N p)) :
    InversionTop.raw (Orb.restrictedO (physicalInversionObservable C N p d x i)) ((),u) =
      wilsonIRSeries C N p d x i (wilsonInversionCoordinates C N p u) := by
  rw [physicalInversion_raw C N p d hC, wilsonIRSeries_develop C N p d x i _ hC]
  congr 1

open BlockGauge BlockGauge.Fabric MultiGauge MultiGauge.Splice MultiGauge.Stack

/-- The genuine finite Schur transaction consumes the actual calibrated
Wilson source, with the supplier’s full vacuum and measure vertices. All lower
account weights and the chosen hierarchy remain those of the supplier. -/
theorem wilsonSchur_physical_source (hC : C.Makes)
    (L : Fabric G (C.side N p)) (T : Cloth L) (w : L.Accounts → PowerSeries ℝ)
    (hw : ∀ a, 0 < PowerSeries.coeff 0 (w a)) (ht : w none = 1)
    (x : Site (C.side N p)) (i : (C.labels.level d).Index) :
    InversionTop.into (Blocking.transaction T
      (evidence _ (enough L T.choose w hw).entire)
      (imbed (attending L (physicalInversionObservable C N p d x i) ∘ T.choose.board))
      (weight (Orb.tray G) (model L T.choose w))) =
        (InversionTop.feed L.even).step (InversionTop.vertices G (C.side N p))
          (fun z => wilsonIRSeries C N p d x i (wilsonInversionCoordinates C N p z.2)) := by
  rw [Blocking.top_projection T w (Orb.traySpec G) hw ht
    (physicalInversion_pretest C N p d hC x i)]
  rw [← InversionTop.tree_agreement L.even
    (physicalInversion_pretest C N p d hC x i).curved]
  congr 1
  funext z
  rcases z with ⟨⟨⟩, u⟩
  exact wilsonInversion_raw_source C N p d hC x i u

variable {I : Type*} (degree : I → ℕ) (positions : I → Site (C.side N p))
    (basis : (j : I) → (C.labels.level (degree j)).Index)

/-- Literal finite products of the same calibrated insertions. -/
def physicalInversionProduct (s : Finset I) : Config G (C.side N p) → ℝ :=
  ∏ j ∈ s, physicalInversionObservable C N p (degree j) (positions j) (basis j)

/-- Passing through the real saddle preserves the literal complex product
of actual calibrated physical insertions. -/
theorem physicalInversionProduct_real (hC : C.Makes) (s : Finset I)
    (U : Config G (C.side N p)) :
    (physicalInversionProduct C N p degree positions basis s U : ℂ) =
      ∏ j ∈ s, C.O N p
        (Dict06.Actual.calibrate C N p (degree j) ((C.labels.level (degree j)).basis (basis j)))
        (positions j) U := by
  rw [physicalInversionProduct, Finset.prod_apply, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun j _ =>
    physicalInversion_real C N p (degree j) hC (positions j) (basis j) U

theorem physicalInversionProduct_pretest (hC : C.Makes) (s : Finset I) :
    Orb.PreTest (physicalInversionProduct C N p degree positions basis s) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [physicalInversionProduct, Finset.prod_empty]
    exact ⟨fun _ _ _ => rfl, Orb.one_test, continuous_const⟩
  | @insert j s hj ih =>
    rw [physicalInversionProduct, Finset.prod_insert hj]
    have hp := physicalInversion_pretest C N p (degree j) hC (positions j) (basis j)
    refine ⟨?_, ⟨hp.curved.boundedness.mul ih.curved.boundedness,
      hp.curved.germ.mul ih.curved.germ⟩, hp.continuous.mul ih.continuous⟩
    intro g hg U
    change physicalInversionObservable C N p (degree j) (positions j) (basis j) (Lattice.gauge g U) *
      physicalInversionProduct C N p degree positions basis s (Lattice.gauge g U) =
        physicalInversionObservable C N p (degree j) (positions j) (basis j) U *
          physicalInversionProduct C N p degree positions basis s U
    rw [hp.gauge g hg U, ih.gauge g hg U]

/-- Products are compiled before the one common normalized expectation;
no product of expectations is substituted. -/
theorem wilsonInversion_raw_product (hC : C.Makes) (s : Finset I)
    (u : Orb.Dir G (C.side N p)) :
    InversionTop.raw (Orb.restrictedO (physicalInversionProduct C N p degree positions basis s)) ((),u) =
      ∏ j ∈ s, wilsonIRSeries C N p (degree j) (positions j) (basis j)
        (wilsonInversionCoordinates C N p u) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [physicalInversionProduct, Finset.prod_empty]
    exact congrFun InversionTop.raw_one ((),u)
  | @insert j s hj ih =>
    rw [physicalInversionProduct, Finset.prod_insert hj]
    change InversionTop.raw
      (Orb.restrictedO (physicalInversionObservable C N p (degree j) (positions j) (basis j)) *
        Orb.restrictedO (physicalInversionProduct C N p degree positions basis s)) ((),u) = _
    rw [InversionTop.raw_mul
      (physicalInversion_pretest C N p (degree j) hC (positions j) (basis j)).curved
      (physicalInversionProduct_pretest C N p degree positions basis hC s).curved]
    rw [Pi.mul_apply]
    rw [wilsonInversion_raw_source C N p (degree j) hC, ih, Finset.prod_insert hj]

/-- The entire actual insertion product enters the same L/T/w finite Schur
transaction and the same normalized terminal feed. Positions may coincide. -/
theorem wilsonSchur_physical_product (hC : C.Makes)
    (L : Fabric G (C.side N p)) (T : Cloth L) (w : L.Accounts → PowerSeries ℝ)
    (hw : ∀ a, 0 < PowerSeries.coeff 0 (w a)) (ht : w none = 1) (s : Finset I) :
    InversionTop.into (Blocking.transaction T
      (evidence _ (enough L T.choose w hw).entire)
      (imbed (attending L (physicalInversionProduct C N p degree positions basis s) ∘ T.choose.board))
      (weight (Orb.tray G) (model L T.choose w))) =
        (InversionTop.feed L.even).step (InversionTop.vertices G (C.side N p))
          (fun z => ∏ j ∈ s, wilsonIRSeries C N p (degree j) (positions j) (basis j)
            (wilsonInversionCoordinates C N p z.2)) := by
  rw [Blocking.top_projection T w (Orb.traySpec G) hw ht
    (physicalInversionProduct_pretest C N p degree positions basis hC s)]
  rw [← InversionTop.tree_agreement L.even
    (physicalInversionProduct_pretest C N p degree positions basis hC s).curved]
  congr 1
  funext z
  rcases z with ⟨⟨⟩, u⟩
  exact wilsonInversion_raw_product C N p degree positions basis hC s u

end YM.Integration
