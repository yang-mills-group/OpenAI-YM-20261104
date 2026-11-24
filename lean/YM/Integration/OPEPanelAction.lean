import YM.Integration.OPEMSReport
import YM.FVA2.ScaleGenerator

/-! All-arity formal correlations of the selected Wilson and independent
MS panels. The ordinary series identity holds in the common nested OPE
basis, for arbitrary fields, at each separated point and each joint test. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPEPanelAction
open Function MeasureTheory PowerSeries RG11.Fields RG11.Jets FVA2 FVA2.Verne Pert.Position
open PositionX PositionX.Jet FVA2.WorldJet FVA2.PayAll
open scoped BigOperators Topology Classical

variable {G : Gauge} {F : Labels.Frames G} {d n : ℕ}

def seriesForm (f : PayAll.reprK F d n) : Court (E F d) n (PowerSeries ℂ) :=
  Attend.raiseW.compMultilinearMap (MultilinearMap.pi (R := ℂ) f)

theorem seriesForm_apply (f : PayAll.reprK F d n) (v : Fin n → E F d) :
    seriesForm f v = PowerSeries.mk (fun k => f k v) := Attend.raised _

theorem renormalized (p : Hop F) (s : ℕ → ℂ) :
    PowerSeries.mk (Jet.ren p.f s) = PowerSeries.subst (deposit (PowerSeries.mk p.f))
      (PowerSeries.mk s) := by
  have hz : Anchored (PowerSeries.mk p.f) := by
    rw [Anchored, ← coeff_zero_eq_constantCoeff_apply, coeff_mk]
    exact p.rooted
  apply PowerSeries.ext
  intro k
  rw [coeff_mk, RadScale.substitute _ p.rooted, coeff_compose _ _ _ (deposit_base _ hz)]
  simp only [← map_pow deposit, deposited, coeff_mk, Complex.real_smul]
  exact Finset.sum_congr rfl fun j _ => mul_comm ..

/-- Evaluation of the full tensor product of input field series and
coupling substitution. The input tuple may have arbitrary coordinates. -/
def converted (p : Hop F) (f : PayAll.reprK F d n) (v : Fin n → E F d) : PowerSeries ℂ :=
  ∑ u : Fin n → (tower F d).toBasis.J,
    (∏ i, WorldJet.style F (p.Z.wire d) (tower F d).b (u i) (v i)) *
      PowerSeries.subst (deposit (PowerSeries.mk p.f))
        (PowerSeries.mk (fun k => f k ((tower F d).b ∘ u)))

private theorem field_action (z : ℕ → Buffer F d) (f : PayAll.reprK F d n)
    (v : Fin n → E F d) :
    PowerSeries.mk (fun k => heated f z k v) =
      ∑ u : Fin n → (tower F d).toBasis.J,
        (∏ i, WorldJet.style F z (tower F d).b (u i) (v i)) *
          PowerSeries.mk (fun k => f k ((tower F d).b ∘ u)) := by
  let t : Test n := 0
  let w := keynote ∘ f
  have hh (k : ℕ) : JetB F (w k) (seriesForm f) t k := by
    change ploy t (keynote (f k)) = _
    rw [heap]
    ext1 v
    change f k v = coeff k (seriesForm f v)
    rw [seriesForm_apply, coeff_mk]
  have he : PowerSeries.mk (fun k => heated f z k v) =
      WorldJet.drag F z (tower F d).b (seriesForm f) v := by
    apply PowerSeries.ext
    intro k
    rw [coeff_mk, WorldJet.drag_h F z (tower F d).b t w v hh]
    rfl
  rw [he, WorldJet.atDrag]
  simp only [seriesForm_apply]

private theorem full_action (p : Hop F) (f : PayAll.reprK F d n) (v : Fin n → E F d) :
    PowerSeries.mk (fun k => heated (Jet.ren p.f f) (p.Z.wire d) k v) =
      converted p f v := by
  rw [field_action, converted]
  apply Finset.sum_congr rfl
  intro u _
  apply congrArg (_ * ·)
  change PowerSeries.mk (taste (Jet.ren p.f f) ((tower F d).b ∘ u)) = _
  rw [PayAll.value_ren, renormalized p]

theorem act_point (P : Panel F) (p : Hop F) (x : Polyp n) (v : Fin n → E F d) :
    PowerSeries.mk (fun k => (Hop.act P p).out d x k v) = converted p (P.out d x) v :=
  full_action p _ _

theorem act_profile (P : Panel F) (hP : P.clearP) (p : Hop F)
    (t : Test n) (v : Fin n → E F d) :
    PowerSeries.mk (fun k => (Hop.act P p).lives d k n t v) =
      converted p (fun k => P.lives d k n t) v := by
  let f : PayAll.reprK F d n := ploy t ∘ P.lives d
  have ht (k : ℕ) : (Hop.act P p).lives d k n t v =
      heated (Jet.ren p.f f) (p.Z.wire d) k v := by
    rw [Hop.act, Panel.turn_book _ _ (Panel.bright P p.f hP), Panel.total_book P p.f hP]
    exact (DFunLike.congr_fun (PayAll.myTip (Jet.ren p.f f) (p.Z.wire d) k t
      (Jet.ren p.f (P.lives d)) (ren_writes (ploy t) p.f (P.lives d))) v).symm
  simp_rw [ht]
  exact full_action p f v

/-- Complex profile testing of the literal separated-kernel panel. -/
def panelTests (P : Panel F) (hP : P.clearP) (k d n : ℕ) :
    Test n →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => E F d) ℂ where
  toFun := P.lives d k n
  map_add' a b := by
    ext1 v
    change P.lives d k n (a+b) v = P.lives d k n a v + P.lives d k n b v
    simp only [Panel.newly P _ _ _ hP, Test.applyTo, _root_.add_apply, add_mul]
    exact integral_add (a.smearing (hP d n k v)) (b.smearing (hP d n k v))
  map_smul' z a := by
    ext1 v
    change P.lives d k n (z • a) v = z • P.lives d k n a v
    simp only [Panel.newly P _ _ _ hP, Test.applyTo, _root_.smul_apply,
      smul_eq_mul, mul_assoc, integral_const_mul]

def panelReport (V : Warehouse G) (P : Panel V.F) (hP : P.Fresh) (hT : Atoll.Towers P) :
    ShapeReport G V.F where
  table := panelTests P hP.1
  maxwell d n t v := by
    change P.lives d 0 n t v = _
    rw [hP.2 d]
    rfl
  packs d e n k h t v := by
    change P.lives d k n t v = P.lives e k n t (RG11.Fields.up V.F h ∘ v)
    rw [OPEMSReport.same_rise V h]
    exact (DFunLike.congr_fun (congrFun (congrFun
      ((Atoll.insist P hP.1).mp hT d e h k) n) t) v).symm

variable (V : Warehouse G) {Q : MS.Land.Booked (FVA2.ColorCode.wings G)}
    (M : MS.Land.MS_Data G Q) {c : ℝ} (B : PositionX.Bend.Booth c V.F)
    (s : ℝ) {hG : G.Simple} (W : Pic.pass V hG M B)

/-- The independent Wilson position normalization as an actual tested
OPE report on the identical physical warehouse. -/
def wilsonReport : ShapeReport G V.F := by
  apply panelReport V (Forge.Check V M B s W) (Forge.nearW V M B s W)
  rw [Forge.agrees]
  apply Atoll.stat (Pic.marked V M s) _ (Pic.clearMark V M s)
  exact fun d e he m x v k => Fountain.tower V M e s v he k x.val

/-- The two independently defined position kernels satisfy the literal
ordinary power-series conversion on every separated configuration. -/
theorem selected_point (x : Polyp n) (v : Fin n → E V.F d) :
    PowerSeries.mk (fun k => (Forge.Check V M B s W).out d x k v) =
      converted (Forge.transfer V M B s W)
        (fun k => Fountain.phys V M s k (x : Points n) d) v := by
  rw [Forge.agrees]
  exact act_point (Pic.marked V M s) _ x v

/-- The same conversion evaluates literally on every smooth joint
test of every arity and field horizon in the independent MS report. -/
theorem selected_profile (t : Test n) (v : Fin n → E V.F d) :
    PowerSeries.mk (fun k => (Forge.Check V M B s W).lives d k n t v) =
      converted (Forge.transfer V M B s W)
        (fun k => (OPEMSReport.report V M s).table k d n t) v := by
  rw [Forge.agrees]
  have hh := act_profile (Pic.marked V M s) (Pic.clearMark V M s)
    (Forge.transfer V M B s W) t v
  rw [Pic.payMark] at hh
  exact hh

end YM.Integration.OPEPanelAction
