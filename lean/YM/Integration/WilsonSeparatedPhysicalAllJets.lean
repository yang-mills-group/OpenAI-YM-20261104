import YM.Integration.WilsonPositionAllRotations
import YM.Integration.WilsonSeparatedPhysicalCameraChange
import YM.Integration.WilsonSeparatedPhysicalOrderedJets

/-! All directional derivatives of the true finite-arity Schwinger hierarchy on an
arbitrary compact subset of configuration space. The source assumes only positive separation
and the actual measured reflected costs of the chosen fields. No ordered time axis is fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalAllJets
open Function Filter Set Extraction Spec Trace Trace.Pilot TraceExtension Climb
open GapsContact GapsContact.Ascent EveryPhase WilsonSeparatedPositionCameras
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {l : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy} {Z : Trace.Terrace.Arch C}

/-- Constants precede the scale, field choices, positions, direction and derivative order. -/
theorem purchased (hG : G.Simple) (bliss : Bliss F l Z H) {n : ℕ} (d : Fin n → ℕ)
    {B : ℝ} (hB : 0 ≤ B) (K : Set (Points n)) (hk : IsCompact K) (clear : K ⊆ conf n) :
    ∃ ρ : ℝ, 0<ρ ∧ ∃ δ∈Ioc (0:ℝ) 1, ∃ A : ℝ, 0≤A ∧ ∃ p : ℕ,
    ∀ᶠ r in trail, ∀ v : (i : Fin n) → S.Field (d i), (∀ i, Ascent.cost F (d i) r (v i) ≤ B) →
      ∀ x∈K, ∀ u : Points n, ‖u‖≤1 → ∀ j : ℕ,
      ‖iteratedDeriv j (fun t : ℝ=> S.classMoment S d (r • (x+t • u)) v) 0‖ ≤
      j.factorial * (A*(LogV r/δ)^p) / ρ^j := by
  choose b hb rot using fun i=>WilsonPositionAllRotations.cost F hG bliss (d i)
  let B' := (∑ i,b i)*B
  have hB' : 0 ≤ B' := mul_nonneg (Finset.sum_nonneg (fun i _=>zero_le_one.trans (hb i))) hB
  have single (i : Fin n) : b i*B ≤ B' := mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f:=b) (fun k _=>zero_le_one.trans (hb k)) (Finset.mem_univ i)) hB
  obtain ⟨P,hp,order,cover⟩ := compact_cover K hk clear
  obtain ⟨ρ,hρ,δ,hδ,A,hA,p,paid⟩ := WilsonSeparatedPhysicalOrderedJets.purchased F hG bliss d hB' P hp
    (fun x hx=>order hx)
  refine ⟨ρ,hρ,δ,hδ,A,hA,p,?_⟩
  filter_upwards [paid,eventually_all.mpr rot,self_mem_nhdsWithin (a:=0)] with r price rotation hr
  intro v bounds x hx u hu j
  obtain ⟨g,σ,member⟩ := cover x hx
  let w := WilsonSeparatedPhysicalCameraChange.field F g σ v
  have budget (i : Fin n) : Ascent.cost F (d (σ i)) r (w i) ≤ B' :=
    (rotation (σ i) g (v (σ i))).trans ((mul_le_mul_of_nonneg_left (bounds (σ i))
      (zero_le_one.trans (hb (σ i)))).trans (single (σ i)))
  have eq := WilsonSeparatedPhysicalCameraChange.along F g σ v (clear hx) u hr
  rw [eq.iteratedDeriv_eq j]
  exact price σ w budget (view g σ x) member (view g σ u) ((size g σ u).trans_le hu) j

end YM.Integration.WilsonSeparatedPhysicalAllJets
