import YM.Integration.SignedWilsonProbeInverse
import YM.Integration.SignedPhysicalWords
import YM.Dash.Limits

/-! Pricing every finite exterior detector on its genuine microscopic Wilson
frame. The same scale carries the measured field and all of its spectators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonExteriorPortfolio
open Function Filter Set Lattice Labels Table Spec Climb OPE OPE.Orbits PhysMS Trace.Pilot Pert.Position
open scoped Topology BigOperators Classical

section Linear
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

def decoder (P : W →ₗ[ℂ] V) (A : V →ₗ[ℂ] W) : W →ₗ[ℂ] V :=
  if h : Bijective (P.comp A) then (LinearEquiv.ofBijective (P.comp A) h).symm.toLinearMap.comp P else 0

def priced (P : W →ₗ[ℂ] V) (A : V →ₗ[ℂ] W) : Prop :=
  (∀ v, decoder P A (A v) = v) ∧
    ∀ y v, ‖decoder P A y-v‖ ≤ (2*‖P.toContinuousLinearMap‖) * ‖y-A v‖

theorem perturbation (P : W →ₗ[ℂ] V) (A : V →ₗ[ℂ] W)
    (hn : ‖(P.comp A).toContinuousLinearMap-(LinearMap.id : V →ₗ[ℂ] V).toContinuousLinearMap‖ ≤ 1/2) :
    priced P A := by
  let Q := P.comp A
  let B := Q.toContinuousLinearMap-(LinearMap.id : V →ₗ[ℂ] V).toContinuousLinearMap
  have small (v : V) : ‖Q v-v‖ ≤ (1/2:ℝ)*‖v‖ :=
    (ContinuousLinearMap.le_opNorm B v).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have lower (v : V) : ‖v‖ ≤ 2*‖Q v‖ := by
    have e : ‖v‖ ≤ ‖Q v-v‖+‖Q v‖ := calc
      ‖v‖ = ‖(v-Q v)+Q v‖ := by rw [sub_add_cancel]
      _ ≤ ‖v-Q v‖+‖Q v‖ := norm_add_le ..
      _ = ‖Q v-v‖+‖Q v‖ := by rw [norm_sub_rev v (Q v)]
    linarith only [small v,e]
  have hi : Injective Q := by
    intro x y h
    have hz : ‖x-y‖ ≤ 0 := by simpa only [map_sub,h,sub_self,norm_zero,mul_zero] using lower (x-y)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)
  have hQ : Bijective Q := ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  let E := LinearEquiv.ofBijective Q hQ
  have de (y : W) : decoder P A y = E.symm (P y) := by rw [decoder,dif_pos hQ]; rfl
  have recovered (z : V) : decoder P A (A z) = z := (de (A z)).trans (E.symm_apply_apply z)
  refine ⟨recovered,?_⟩
  intro y z
  have bound (u : W) : ‖decoder P A u‖ ≤ (2*‖P.toContinuousLinearMap‖)*‖u‖ := by
    have eq : Q (decoder P A u) = P u := (congrArg Q (de u)).trans (E.apply_symm_apply _)
    calc
      _ ≤ 2*‖Q (decoder P A u)‖ := lower _
      _ = 2*‖P u‖ := by rw [eq]
      _ ≤ 2*(‖P.toContinuousLinearMap‖*‖u‖) := mul_le_mul_of_nonneg_left
        (P.toContinuousLinearMap.le_opNorm _) (by norm_num)
      _ = _ := (mul_assoc _ _ _).symm
  simpa only [map_sub,recovered] using bound (y-A z)

theorem stable {α : Type*} (l : Filter α) (P : W →ₗ[ℂ] V) (A : α → V →ₗ[ℂ] W)
    (h : ∀ z : V, Tendsto (fun t => P (A t z)) l (𝓝 z)) :
    ∀ᶠ t in l, priced P (A t) := by
  have lim := Dash.fit_plane (fun t => P.comp (A t)) (LinearMap.id : V →ₗ[ℂ] V) h
  filter_upwards [Metric.tendsto_nhds.mp lim (1/2) (by norm_num)] with t ht
  exact perturbation P (A t) (by simpa only [dist_eq_norm] using ht.le)
end Linear

section Geometry
variable {G : Gauge} {L : Register G} (T : Table L)
def points (E : ExteriorData T) := Points.cons 0 (OPE.positions T E)
def word {d : ℕ} (E : ExteriorData T) (z : T.Field d) : Fin (E.length+1) → T.Tag :=
  Fin.cons ⟨d,z⟩ (OPE.tags T E)
end Geometry

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hS : Services C f S)
local notation "F₀" => Bel C.book
def carried (r : ℝ) (v : (Bel C.book).Tag) : S.Tag := ⟨v.1,J r v.1 v.2⟩
def token (r : ℝ) (v : (Bel C.book).Tag) := OPE.detectorRaw S (carried J r v)

def row (T : Table C.book) (r : ℝ) (D : ℕ) (e : ExteriorData F₀) : E C.labels D →ₗ[ℂ] ℂ :=
  (T.injectFront (fun i : Fin e.length => token J r (OPE.tags F₀ e i)) (r • points F₀ e) D).comp
    ((S.representative D).comp (J r D).toLinearMap)

theorem row_read (T : Table C.book) (r : ℝ) (D : ℕ) (e : ExteriorData F₀) (v : E C.labels D) :
    row J T r D e v = T.read (r • points F₀ e) (token J r ∘ word F₀ e v) := by
  change T.read (r • points F₀ e) (Fin.cons (⟨D,S.representative D (J r D v)⟩ : C.book.Token)
    (fun i => token J r (OPE.tags F₀ e i))) = _
  apply congrArg (T.read (r • points F₀ e))
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

include F in
theorem original {D : ℕ} (e : ExteriorData F₀) (r : ℝ) (v : E C.labels D) (a : ℕ × ℕ)
    (j : ℕ) (hj : j ≤ a.1) :
    row J (StressFlux.Matching.rounded C a.1 a.2) r D e v =
      SignedPhysicalWords.sample (carried J r ∘ word F₀ e v) (r • points F₀ e) a j hj := by
  simp only [row_read,SignedPhysicalWords.sample,SignedTreeTransport.mean_eq F.room.cutoff _ _ _ _ _
    (WilsonWholeLimit.product_continuous ..)]
  rfl

include hJ in
theorem running {D : ℕ} (e : ExteriorData F₀) (he : Apt e) (v : E C.labels D) :
    Tendsto (fun r => row J S r D e v) trail (𝓝 (witnessAt F₀ D e v)) := by
  let w := word F₀ e v
  have h := PhysMS.leading_at F hJ (d := fun i => (w i).1) (fun i => (w i).2)
    tendsto_id tendsto_const_nhds (generic_conf (e.length+1) he)
  have href : witnessAt F₀ D e v = PhysMS.WickGoal (C := C) (d := fun i => (w i).1)
      (fun i => (w i).2) (points F₀ e) := by
    exact witness_kernel (S := F₀) (T := F₀) v e
  have hrow (r : ℝ) : row J S r D e v = PhysMS.measured F none (J r) (d := fun i => (w i).1)
      (fun i => (w i).2) r (points F₀ e) := by
    exact row_read J S r D e v
  rw [href]
  exact h.congr (fun r => (hrow r).symm)

def bank {D : ℕ} (U : Detector F₀ D) (T : Table C.book) (r : ℝ) :
    E C.labels D →ₗ[ℂ] (Fin U.size → ℂ) := LinearMap.pi (fun i => row J T r D (U.listen i))

def readings {D : ℕ} (U : Detector F₀ D) (v : E C.labels D) : Fin U.size → ℂ :=
  fun i => witnessAt F₀ D (U.listen i) v

include hJ in
theorem continuum {D : ℕ} (U : Detector F₀ D) (v : E C.labels D) :
    Tendsto (fun r => bank J U S r v) trail (𝓝 (readings U v)) :=
  tendsto_pi_nhds.mpr (fun i => running F J hJ (U.listen i) (U.awake i) v)

include hJ hS in
theorem regulated {D : ℕ} (U : Detector F₀ D) (v : E C.labels D) :
    Tendsto (fun p : ℝ × (ℕ × ℕ) => bank J U (StressFlux.Matching.rounded C p.2.1 p.2.2) p.1 v)
      (trail.curry f.fuse) (𝓝 (readings U v)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h₁ := running F J hJ (U.listen i) (U.awake i) v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply eventually_curry_iff.mpr
  filter_upwards [Metric.tendsto_nhds.mp h₁ (ε/2) (half_pos hε),self_mem_nhdsWithin] with r ho hp
  let x := points F₀ (U.listen i)
  let w := token J r ∘ word F₀ (U.listen i) v
  have h₂ := WilsonWholeLimit.rounded_tendsto_separated F hS w (r • x)
    (Work.A05.smul_conf hp (generic_conf ((U.listen i).length+1) (U.awake i)))
  filter_upwards [Metric.tendsto_nhds.mp h₂ (ε/2) (half_pos hε)] with a ha
  change dist (row J (StressFlux.Matching.rounded C a.1 a.2) r D (U.listen i) v)
    (witnessAt F₀ D (U.listen i) v) < ε
  have h₃ : dist (row J (StressFlux.Matching.rounded C a.1 a.2) r D (U.listen i) v)
      (row J S r D (U.listen i) v) < ε/2 := by simpa only [row_read] using ha
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add h₃ ho).trans_eq (add_halves ε))

set_option maxHeartbeats 600000 in
include hJ hS in
theorem portfolio {D : ℕ} (U : Detector F₀ D) :
    (∀ᶠ r in trail, priced U.report (bank J U S r)) ∧
    ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse, priced U.report
      (bank J U (StressFlux.Matching.rounded C a.1 a.2) r) := by
  have h {α : Type} (l : Filter α) (A : α → E C.labels D →ₗ[ℂ] (Fin U.size → ℂ))
      (hh : ∀ v, Tendsto (fun t => A t v) l (𝓝 (readings U v))) :
      ∀ᶠ t in l, priced U.report (A t) := by
    apply stable
    intro v
    have he : Tendsto (fun t => U.report (A t v)) l (𝓝 (U.report (readings U v))) :=
      U.report.continuous_of_finiteDimensional.continuousAt.tendsto.comp (hh v)
    have hr : U.report (readings U v) = v := U.recovered v
    rw [hr] at he
    exact he
  let A (r : ℝ) := bank J U S r
  let B (p : ℝ × (ℕ × ℕ)) := bank J U (StressFlux.Matching.rounded C p.2.1 p.2.2) p.1
  have hc : ∀ᶠ r in trail, priced U.report (A r) := h trail A (continuum F J hJ U)
  have hf : ∀ᶠ p in trail.curry f.fuse, priced U.report (B p) :=
    h (trail.curry f.fuse) B (regulated F J hJ hS U)
  exact ⟨hc,eventually_curry_iff.mp hf⟩
def samples {D : ℕ} (U : Detector F₀ D) (r : ℝ) (a : ℕ × ℕ) (j : ℕ) (hj : j ≤ a.1)
    (v : E C.labels D) : Fin U.size → ℂ := fun i =>
  SignedPhysicalWords.sample (carried J r ∘ word F₀ (U.listen i) v) (r • points F₀ (U.listen i)) a j hj

include F in
theorem samples_eq {D : ℕ} (U : Detector F₀ D) (r : ℝ) (a : ℕ × ℕ) (j : ℕ) (hj : j ≤ a.1)
    (v : E C.labels D) : samples J U r a j hj v = bank J U (StressFlux.Matching.rounded C a.1 a.2) r v :=
  funext fun i => (original F J (U.listen i) r v a j hj).symm

def usable {D : ℕ} (U : Detector F₀ D) (r : ℝ) (a : ℕ × ℕ) : Prop :=
  let A := bank J U (StressFlux.Matching.rounded C a.1 a.2) r
  ∀ j (hj : j ≤ a.1), (∀ v, decoder U.report A (samples J U r a j hj v) = v) ∧
    ∀ y v, ‖decoder U.report A y-v‖ ≤ (2*‖U.report.toContinuousLinearMap‖) * ‖y-samples J U r a j hj v‖

include hJ hS in
theorem windows {ι : Type*} [Fintype ι] (D : ι → ℕ) (U : (i : ι) → Detector F₀ (D i)) :
    ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse, ∀ i, usable J (U i) r a := by
  have paid (i : ι) : ∀ᶠ t : ℝ × (ℕ × ℕ) in trail.curry f.fuse, usable J (U i) t.1 t.2 := by
    apply eventually_curry_iff.mpr
    filter_upwards [(portfolio F J hJ hS (U i)).2] with r hr
    filter_upwards [hr] with a ha
    intro j hj
    constructor
    · intro v
      rw [samples_eq F J (U i) r a j hj v]
      exact ha.1 v
    · intro y v
      rw [samples_eq F J (U i) r a j hj v]
      exact ha.2 y v
  exact eventually_curry_iff.mp (eventually_all.mpr paid)

end YM.Integration.WilsonExteriorPortfolio
