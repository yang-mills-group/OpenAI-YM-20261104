import YM.Integration.WilsonPositionHomogeneousLeading
import YM.RG05Readout.Bay.Masthead

/-! A finite family of genuine separated ultraviolet probes controls the inverse
running frame on the complete quotient. The exterior insertions run in the same
homogeneous physical frame at the same radius as the unknown central field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
open Function Filter Set Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open scoped Topology ContDiff Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {Y : (Bel R.family.book).Hierarchy} (lead : PhysMS.Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d) (simple : G.Simple) {d : ℕ}

private def companion (r : ℝ) (t : R.family.book.Token) : R.family.book.Token :=
  ⟨t.1,S.representative t.1 (homogeneous F J Z r t.1 ((Bel R.family.book).project t.1 t.2))⟩

def probe (e : Exterior (standard R.family.book.grid)) (r : ℝ) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  (S.injectFront (companion F J Z r ∘ e.letter) (r • e.point) d).comp (S.representative d)

private theorem zeroth {n : ℕ} (a b : Points n → ℂ) (p : Points n) :
    ‖iteratedFDeriv ℝ 0 a p - iteratedFDeriv ℝ 0 b p‖ = ‖a p-b p‖ := by
  rw [show iteratedFDeriv ℝ 0 a p - iteratedFDeriv ℝ 0 b p = iteratedFDeriv ℝ 0 (a-b) p by ext z; simp,
    norm_iteratedFDeriv_zero]
  rfl

include lead paid simple in
theorem point (e : Exterior (standard R.family.book.grid)) (x : (Bel R.family.book).Field d) :
    Tendsto (fun r => probe F J Z e r d (homogeneous F J Z r d x)) trail (𝓝 ((Bel R.family.book).spectra d x e)) := by
  let B := Bel R.family.book
  obtain ⟨v,rfl⟩ := B.onto d x
  let p : Fin (e.n+1) → R.family.book.Token := Fin.cons ⟨d,v⟩ e.letter
  let h (j : Fin (e.n+1)) := (p j).1
  let src (j : Fin (e.n+1)) : B.Field (h j) := B.project (h j) (p j).2
  have literal (r : ℝ) : probe F J Z e r d (homogeneous F J Z r d (B.project d v)) =
      S.classMoment S h (r • e.point) (fun j => homogeneous F J Z r (h j) (src j)) := by
    change S.read (r • e.point) (Fin.cons (companion F J Z r ⟨d,v⟩) (companion F J Z r ∘ e.letter)) =
      S.read (r • e.point) (companion F J Z r ∘ p)
    congr 1
    funext i
    refine Fin.cases (by rfl) (fun j => ?_) i
    rfl
  have free : B.classMoment B h e.point src = B.spectra d (B.project d v) e := by
    exact B.class_agrees B Y.laws.toSymmetric (fun _ => le_rfl) h e.clear (fun i => (p i).2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have price := WilsonPositionHomogeneousLeading.jets F J Z lead paid simple h src 0
    (K:={e.point}) isCompact_singleton (Set.singleton_subset_iff.mpr e.clear) (half_pos hε)
  filter_upwards [price] with r hr
  have scalar := hr e.point (Set.mem_singleton _)
  rw [zeroth] at scalar
  rw [dist_eq_norm,literal,← free]
  exact lt_of_le_of_lt scalar (half_lt_self hε)

variable (D : Contacts.Foci (Bel R.family.book) d)

def readout (r : ℝ) : S.Field d →ₗ[ℂ] (D.index → ℂ) := LinearMap.pi fun i => probe F J Z (D.shell i) r d

def reference : (Bel R.family.book).Field d →ₗ[ℂ] (D.index → ℂ) :=
  LinearMap.pi fun i => (LinearMap.proj (D.shell i)).comp ((Bel R.family.book).spectra d)

def running (r : ℝ) : (Bel R.family.book).Field d →ₗ[ℂ] (D.index → ℂ) :=
  (readout F J Z D r).comp (homogeneous F J Z r d).toLinearMap

include lead paid simple in
theorem converges : Tendsto (fun r => (running F J Z D r).toContinuousLinearMap) trail
    (𝓝 (reference D).toContinuousLinearMap) := by
  apply Dash.fit_plane
  intro x
  exact tendsto_pi_nhds.mpr fun i => point F J Z lead paid simple (D.shell i) x

include lead paid simple in
/-- A fixed, positive normalized decoder price applies to every central field at once. -/
theorem stability : ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail, ∀ y : S.Field d,
    ‖(homogeneous F J Z r d).symm y‖ ≤ K * ‖readout F J Z D r y‖ := by
  let q := D.decoder.toContinuousLinearMap
  let C := ‖q‖+1
  have pos : 0 < C := by dsimp [C]; positivity
  have first (x : (Bel R.family.book).Field d) : ‖x‖ ≤ C * ‖reference D x‖ := by
    calc
      ‖x‖ = ‖q (reference D x)‖ := congrArg norm (D.detects x).symm
      _ ≤ ‖q‖ * ‖reference D x‖ := q.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)
  let basis := Module.finBasis ℂ ((Bel R.family.book).Field d)
  let charge (i : Fin (Module.finrank ℂ ((Bel R.family.book).Field d))) := ‖(basis.coord i).toContinuousLinearMap‖
  let W := (∑ i, charge i)+1
  have Wpos : 0 < W := by dsimp [W,charge]; positivity
  let θ := (2*C*W)⁻¹
  have θpos : 0 < θ := by dsimp [θ]; positivity
  have close : ∀ᶠ r in trail, ∀ i, ∀ j : D.index,
      ‖reference D (basis i) j - running F J Z D r (basis i) j‖ ≤ θ := by
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    have hit := Metric.tendsto_nhds.mp (point F J Z lead paid simple (D.shell j) (basis i)) θ θpos
    filter_upwards [hit] with r hr
    rw [dist_eq_norm] at hr
    exact (norm_sub_rev ..).le.trans hr.le
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [close] with r hr y
  let x := (homogeneous F J Z r d).symm y
  let A := running F J Z D r
  let V := reference D
  have column (i) : ‖(V-A) (basis i)‖ ≤ θ := by
    apply (pi_norm_le_iff_of_nonneg θpos.le).mpr
    exact hr i
  have weights : ∑ i, ‖basis.coord i x‖ ≤ (∑ i, charge i)*‖x‖ := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => (basis.coord i).toContinuousLinearMap.le_opNorm x
  have repr : (∑ i, basis.coord i x • basis i) = x := basis.sum_repr x
  have error : ‖V x - A x‖ ≤ θ*W*‖x‖ := by
    calc
      _ = ‖(V-A) (∑ i, basis.coord i x • basis i)‖ := by rw [repr]; rfl
      _ = ‖∑ i, basis.coord i x • (V-A) (basis i)‖ := by simp only [map_sum,map_smul]
      _ ≤ ∑ i, ‖basis.coord i x‖ * ‖(V-A) (basis i)‖ := by simpa only [norm_smul] using norm_sum_le Finset.univ (fun i => basis.coord i x • (V-A) (basis i))
      _ ≤ ∑ i, ‖basis.coord i x‖ * θ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (column i) (norm_nonneg _)
      _ = (∑ i, ‖basis.coord i x‖)*θ := (Finset.sum_mul ..).symm
      _ ≤ ((∑ i, charge i)*‖x‖)*θ := mul_le_mul_of_nonneg_right weights θpos.le
      _ ≤ θ*W*‖x‖ := by dsimp [W]; nlinarith only [mul_nonneg θpos.le (norm_nonneg x)]
  have triangle : ‖V x‖ ≤ ‖V x-A x‖ + ‖A x‖ := by simpa only [sub_add_cancel] using norm_add_le (V x-A x) (A x)
  have measured : ‖V x‖ ≤ θ*W*‖x‖ + ‖A x‖ := triangle.trans (add_le_add error le_rfl)
  have paid' := (first x).trans (mul_le_mul_of_nonneg_left measured pos.le)
  have absorb : C*(θ*W*‖x‖ + ‖A x‖) = ‖x‖/2 + C*‖A x‖ := by dsimp [θ]; field_simp [ne_of_gt pos,ne_of_gt Wpos]
  rw [absorb] at paid'
  have result : ‖x‖ ≤ 2*C*‖A x‖ := by linarith
  have observed : A x = readout F J Z D r y := by
    change readout F J Z D r (homogeneous F J Z r d ((homogeneous F J Z r d).symm y)) = _
    rw [LinearEquiv.apply_symm_apply]
  rwa [observed] at result

include lead paid simple in
theorem original (d : ℕ) : ∃ D : Contacts.Foci (Bel R.family.book) d, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ r in trail, ∀ y : S.Field d, ‖(homogeneous F J Z r d).symm y‖ ≤ K * ‖readout F J Z D r y‖ := by
  obtain ⟨D⟩ := Contacts.Foci.available Y.translations d
  exact ⟨D,stability F J Z lead paid simple D⟩

end YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
