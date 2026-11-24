import YM.Integration.WilsonSeparatedPhysicalAllJets

/-! The actual holomorphic one-variable model behind the compact noncollision hierarchy
estimate. Every admissible finite field roster uses one disc radius before the physical scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalDisc
open Function Filter Set Metric Extraction Spec Trace Trace.Pilot TraceExtension Climb
open Boundary Boundary.Surface GapsContact GapsContact.Ascent GapsContact.Tunnel EveryPhase
open WilsonSeparatedTubeCoordinates WilsonSeparatedPositionCameras
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {l : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}

theorem model (hG : G.Simple) (bliss : Bliss F l Z H) {n : ℕ} (d : Fin n → ℕ)
    {B : ℝ} (hB : 0≤B) (K : Set (Points n)) (hk : IsCompact K) (clear : K ⊆ conf n) :
    ∃ ρ : ℝ, 0<ρ ∧ ∃ δ∈Ioc (0:ℝ) 1, ∃ A : ℝ, 0≤A ∧ ∃ p : ℕ,
    ∀ᶠ r in trail, ∀ x∈K, ∀ u : Points n, ‖u‖≤1 → ∀ v : (i : Fin n) → S.Field (d i),
      (∀ i, Ascent.cost F (d i) r (v i) ≤ B) → ∃ g : ℂ→ℂ,
      AnalyticOnNhd ℂ g (closedBall 0 ρ) ∧ (∀ z∈closedBall 0 ρ, ‖g z‖≤A*(LogV r/δ)^p) ∧
      ((fun t : ℝ=>S.classMoment S d (r • (x+t • u)) v) =ᶠ[𝓝 0] fun t : ℝ=>g t) := by
  obtain ⟨P,hp,order,cover⟩ := compact_cover K hk clear
  let e : Points n →L[ℝ] Full n := embedding.comp coordinates
  have inside : e '' P ⊆ tube n := by
    rintro _ ⟨q,hq,rfl⟩
    exact plane_inside (coordinates q).1 (order hq)
  obtain ⟨ρ,hρ,thick⟩ := (hp.image e.continuous).exists_cthickening_subset_open (south n) inside
  have hcompact : IsCompact (cthickening ρ (e '' P)) := (hp.image e.continuous).cthickening
  obtain ⟨δ,⟨room,hδ⟩,hle⟩ := (((Room.compact hcompact thick).and
    (show ∀ᶠ d : ℝ in trail, 0<d from self_mem_nhdsWithin)).and
    ((ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)).exists
  choose b hb rot using fun i=>WilsonPositionAllRotations.cost F hG bliss (d i)
  let B' := (∑ i,b i)*B
  have nonneg : 0≤B' := mul_nonneg (Finset.sum_nonneg (fun i _=>zero_le_one.trans (hb i))) hB
  have single (i : Fin n) : b i*B ≤ B' := mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f:=b) (fun k _=>zero_le_one.trans (hb k)) (Finset.mem_univ i)) hB
  obtain ⟨L⟩ := almanac F
  obtain ⟨Y,-,seen⟩ := (Survey.fits L (none : Survey F)).reveals
  obtain ⟨D,X,-⟩ := (seen F.action.J F.realization.qt.induced).1.visible
  obtain ⟨A,hA,p,paid⟩ := WilsonSeparatedTubeEnvelope.purchased F hG bliss L d nonneg
  refine ⟨ρ,hρ,δ,⟨hδ,hle⟩,A,hA,p,?_⟩
  filter_upwards [paid,eventually_all.mpr rot,self_mem_nhdsWithin (a:=0)] with r price rotation hr
  intro x hx u hu
  obtain ⟨h,σ,member⟩ := cover x hx
  let q := view h σ x
  let a := view h σ u
  let axis (z : ℂ) := e q+z • e a
  have len : ‖e a‖≤1 := (WilsonSeparatedTubeCoordinates.isometry a).trans_le ((size h σ u).trans_le hu)
  have hits : MapsTo axis (closedBall 0 ρ) (cthickening ρ (e '' P)) := by
    intro z hz
    apply mem_cthickening_of_dist_le _ (e q) ρ _ (mem_image_of_mem e member)
    have hz' : ‖z‖≤ρ := by simpa using hz
    rw [dist_eq_norm]
    dsimp only [axis]
    rw [add_sub_cancel_left,norm_smul]
    exact (mul_le_of_le_one_right (norm_nonneg _) len).trans hz'
  intro v bounds
  let w := WilsonSeparatedPhysicalCameraChange.field F h σ v
  have budget (i : Fin n) : Ascent.cost F (d (σ i)) r (w i)≤B' :=
    (rotation (σ i) h (v (σ i))).trans ((mul_le_mul_of_nonneg_left (bounds (σ i))
      (zero_le_one.trans (hb (σ i)))).trans (single (σ i)))
  let film := weather X (WilsonSeparatedTubeEnvelope.tag w) r
  obtain ⟨hol,bill⟩ := price σ w budget none D X
  have ax (z : ℂ) : AnalyticAt ℂ axis z := by dsimp [axis]; fun_prop
  refine ⟨fun z=>film (axis z),fun z hz=>(hol _ (thick (hits hz))).comp (ax z),
    fun z hz=>bill δ ⟨hδ,hle⟩ _ (room _ (hits hz)),?_⟩
  have prior := WilsonSeparatedPhysicalCameraChange.along F h σ v (clear hx) u hr
  apply prior.trans
  have c : Continuous (fun t : ℝ => (coordinates (q+t • a)).2) := by fun_prop
  have origin : (coordinates (q+(0:ℝ) • a)).2 ∈ east n := by
    rw [zero_smul,add_zero]
    exact order member
  filter_upwards [c.continuousAt.eventually ((open_east n).mem_nhds origin)] with t ht
  have hread := (WilsonSeparatedTubePhysicalPlane.read F L D X w hr (coordinates (q+t • a)).1
    (coordinates (q+t • a)).2 ht).symm
  rw [rebuild] at hread
  calc _ = film (e (q+t • a)) := hread
       _ = _ := by simp only [axis,map_add,map_smul,Complex.coe_smul]

end YM.Integration.WilsonSeparatedPhysicalDisc
