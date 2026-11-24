import YM.OPE.Orbits.Kernel
import YM.OPE.ElementaryLog

/-! At each retained grade the public real covariant reader and the projected raw
prescription agree to one higher spatial order, for the same fixed physical labels. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicProjectedRow
open Function Set Filter MeasureTheory Table Extraction OPE OPE.Orbits OPE.Orbits.Reader
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (F : Spec.Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I : Type} [Fintype I] {d : I → ℕ} (v : Labels S d)

/-- The projected unaveraged sum at the grade being measured. -/
def raw (m : ℕ) (x : I → E4) (o : E4) : S.Field m :=
    Q.cutTest m m (shadowOld Q.port m x o v)

theorem bridge (paid : Services C f S) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η)
    (m : ℕ) :
    ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I → E4) (o : E4), WithinRoom r M η x o →
      ‖Q.fresh m x o v - raw F Q v m x o‖ ≤ r ^ ((m:ℝ) - weight d + 1/2) := by
  let P (r:ℝ) (z:(I→E4)×E4) := WithinRoom r M η z.1 z.2
  let V (r:ℝ) (z:(I→E4)×E4) :=
    ‖Q.fresh m z.1 z.2 v - raw F Q v m z.1 z.2‖ ≤ r ^ ((m:ℝ)-weight d+1/2)
  have h : ∀ᶠ r:ℝ in 𝓝[>]0, ∀ z, P r z → V r z := by
    apply refine_geometry
    intro z ψ hψ hl hz
    letI := hψ
    have hr : Tendsto id ψ (𝓝[>] (0:ℝ)) := tendsto_id.mono_left hl
    obtain ⟨hx,hk⟩ := room_regime (r:=id) (φ:=ψ)
      (X:=fun i => (z i).1) (O:=fun i => (z i).2) hr hM hη hz
    have hT := run_towards hr
    have hb := fresh_bridge (o:=fun i => (z i).2) (v:=v) F Q paid hT hx hk zero_lt_one m m
    exact ⟨_,hψ,le_rfl, ((loglife hr).rpow ((m:ℝ)-weight d+1/2)).outweigh hb (by linarith) hT⟩
  filter_upwards [h] with r hr x o fit using hr (x,o) fit

/-- Only modes of precisely the projected grade have a nonzero raw contribution. -/
theorem exact_grade (m : ℕ) (x : I → E4) (o : E4) :
    raw F Q v m x o = ∑ j ∈ (bands F.sector.derivatives m).filter (fun j => j.fst = m),
      Q.port.ope j x (names v) o • Q.cutTest m m (Q.port.loaded j m) := by
  unfold raw shadowOld shadow
  simp only [map_sum,map_smul]
  symm
  apply Finset.sum_subset (Finset.filter_subset ..)
  intro j hj hn
  have hle : j.fst ≤ m := (full_bands ..).mp hj
  have hlt : j.fst < m := lt_of_le_of_ne hle (fun he => hn (Finset.mem_filter.mpr ⟨hj,he⟩))
  rw [Q.port.cost j hj, Q.cut_rise m j.fst m hle, Q.kills_lower m j.fst hlt, smul_zero]

end YM.Integration.WilsonMacroscopicProjectedRow
