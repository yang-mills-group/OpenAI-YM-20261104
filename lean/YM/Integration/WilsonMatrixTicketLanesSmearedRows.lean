import YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
import YM.Integration.WilsonPositionPhaseProfileTest

/-! Normalized smooth signed exterior readings on the physical run, linear in
the unknown quotient field and converging to the actual Maxwell readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesSmearedRows
open Function Set Filter MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open private companion zeroth from YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
open scoped Topology ContDiff Classical
variable {G : Gauge} {L : Register G} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {Y : (Bel R.family.book).Hierarchy} (lead : PhysMS.Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d) (simple : G.Simple) {d n : ℕ}

private def zoom (T : Table L) (r : ℝ) : Table L where value h z := T.value h (r • z)

private theorem integrable (T : Table L) (reg : T.Smooth) {r : ℝ} (hr : 0 < r) : Dash.Live (zoom T r) := by
  intro n p φ
  apply φ.smearing
  apply (T.smooth_read reg p).continuousOn.comp
  · fun_prop
  · exact fun z hz => Work.A05.smul_conf hr hz

private theorem direct (T : Table L) (reg : T.Smooth) : Dash.Live T := fun _ p φ => φ.smearing (T.smooth_read reg p).continuousOn

private def shot (tail : Fin n → L.Token) (φ : Test (n+1)) : Dash.Shot L :=
  ⟨n+1,0,Fin.cons ⟨0,0⟩ tail,φ⟩

private theorem scored (T : Table L) (live : Dash.Live T) (tail : Fin n → L.Token) (φ : Test (n+1)) (u : L.Ref d) :
    (shot tail φ).core T live u = φ.applyTo (fun z => T.read z (Fin.cons ⟨d,u⟩ tail)) := by
  change φ.applyTo (fun z => T.read z ((shot tail φ).record u)) = _
  have insert : (shot tail φ).record u = Fin.cons ⟨d,u⟩ tail  := by
    funext i
    refine Fin.cases (by simp [Dash.Shot.record,shot]) (fun j => ?_) i
    simp [Dash.Shot.record,shot]
  rw [insert]

variable (e : Exterior (standard R.family.book.grid)) (φ : Test (e.n+1))

def freeKernel (x : (Bel R.family.book).Field d) (z : Points (e.n+1)) : ℂ :=
  (Bel R.family.book).read z (Fin.cons ⟨d,(Bel R.family.book).representative d x⟩ e.letter)

def physicalKernel (r : ℝ) (y : S.Field d) (z : Points (e.n+1)) : ℂ :=
  S.read (r • z) (Fin.cons ⟨d,S.representative d y⟩ (companion F J Z r ∘ e.letter))

/-- Each row is a complex linear map on the genuine physical quotient. -/
def observation (r : ℝ) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ := if hr : 0 < r then
  ((shot (companion F J Z r ∘ e.letter) φ).core (zoom S r) (integrable S F.room.kernel.smooth hr)).toLinearMap.comp (S.representative d)
  else 0

def tree (Y : (Bel R.family.book).Hierarchy) (d : ℕ) : (Bel R.family.book).Field d →ₗ[ℂ] ℂ :=
  ((shot e.letter φ).core (Bel R.family.book) (direct (Bel R.family.book) Y.smooth)).toLinearMap.comp ((Bel R.family.book).representative d)

theorem on_field {r : ℝ} (hr : 0 < r) (y : S.Field d) : observation F J Z e φ r d y = φ.applyTo (physicalKernel F J Z e r y) := by
  rw [observation,dif_pos hr]
  exact scored (zoom S r) (integrable S F.room.kernel.smooth hr) (companion F J Z r ∘ e.letter) φ (S.representative d y)

theorem on_tree (x : (Bel R.family.book).Field d) : tree e φ Y d x = φ.applyTo (freeKernel e x) :=
  scored (Bel R.family.book) (direct (Bel R.family.book) Y.smooth) e.letter φ ((Bel R.family.book).representative d x)

theorem known (x : (Bel R.family.book).Field d) : freeKernel e x e.point = (Bel R.family.book).spectra d x e := by
  let B := Bel R.family.book
  change B.replies d (B.representative d x) e = B.spectra d x e
  rw [← B.projected, B.rep]

include lead paid simple in
theorem converges (x : (Bel R.family.book).Field d) :
    Tendsto (fun r => observation F J Z e φ r d (homogeneous F J Z r d x)) trail (𝓝 (tree e φ Y d x)) := by
  let B := Bel R.family.book
  let p : Fin (e.n+1) → (standard R.family.book.grid).Token := Fin.cons ⟨d,B.representative d x⟩ e.letter
  let h (i : Fin (e.n+1)) := (p i).1
  let src (i : Fin (e.n+1)) : B.Field (h i) := B.project (h i) (p i).2
  have literal (r : ℝ) (z : Points (e.n+1)) : physicalKernel F J Z e r (homogeneous F J Z r d x) z =
      S.classMoment S h (r • z) (fun i => homogeneous F J Z r (h i) (src i)) := by
    change S.read (r • z) (Fin.cons ⟨d,S.representative d (homogeneous F J Z r d x)⟩ (companion F J Z r ∘ e.letter)) =
      S.read (r • z) (companion F J Z r ∘ p)
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => (by rfl)) i
    change (⟨d,S.representative d (homogeneous F J Z r d x)⟩ : R.family.book.Token) = ⟨d,S.representative d (homogeneous F J Z r d (B.project d (B.representative d x)))⟩
    rw [B.rep]
  have free (z : Points (e.n+1)) (hz : z ∈ conf (e.n+1)) : B.classMoment B h z src = freeKernel e x z :=
    B.class_agrees B Y.laws.toSymmetric (fun _ => le_rfl) h hz (fun i => (p i).2)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let c := WilsonPositionPhaseProfileTest.mass φ
  have nc : 0 ≤ c := integral_nonneg fun _ => norm_nonneg _
  let η := ε/(2*(c+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have cost : c*η < ε := by
    dsimp [η]; rw [← mul_div_assoc]; apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith only [hε,mul_nonneg nc hε.le]
  have jets := WilsonPositionHomogeneousLeading.jets F J Z lead paid simple h src 0 φ.hasCompactSupport φ.tsupport_subset hη
  filter_upwards [jets, self_mem_nhdsWithin] with r hr positive
  rw [dist_eq_norm,on_field F J Z e φ positive,on_tree e φ]
  apply lt_of_le_of_lt _ cost
  apply WilsonPositionPhaseProfileTest.price
  · exact (integrable S F.room.kernel.smooth positive) _ _ φ
  · exact (direct (Bel R.family.book) Y.smooth) _ _ φ
  · intro z hz
    have pt := hr z hz
    rw [zeroth,← literal,free z (φ.tsupport_subset hz)] at pt
    exact pt

end YM.Integration.WilsonMatrixTicketLanesSmearedRows
