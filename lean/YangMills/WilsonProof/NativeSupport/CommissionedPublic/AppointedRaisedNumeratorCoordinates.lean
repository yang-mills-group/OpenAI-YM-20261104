import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedFiniteNumeratorOrdinary

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace YM.FVA2.GradedFar.AppointedRaisedNumerator
noncomputable section
open Filter Function Real Set MeasureTheory PowerSeries
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window OPE Orbits Physical
open YangMills YM.Answer.ContinuumLimit YM.Integration Asymptotics
open scoped Topology BigOperators Classical ContDiff

universe u v
variable {G : Gauge} {n h : ℕ} {e : Fin n → ℕ}

/-- The finite tensor expression has the same input, output and scale as the prescribed book. -/
abbrev filedSeries (N : Register.WilsonPrescription G) (x : Points n)
    (a : (i : Fin n) → Sec G (e i)) (l : Toon G h) : PowerSeries ℂ :=
  ∑ b : (i : Fin n) → Toon G (e i), PowerSeries.C (∏ i, coord (b i) (a i)) *
    FarCoefficients (Measure.outlook N.scheme N.criterion) (fun i => flash (b i)) x (flash l)

theorem prescribed (N : Register.WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
    (x : Points n) (a : (i : Fin n) → Sec G (e i)) (l : Toon G h) (q : ℕ) (t : ℝ) :
    coord l (Wave.cropped N M x a h q t) = crop q t (filedSeries N x a l) := by
  rw [Wave.fee N M H x a q h t, coord_actual]
  rfl

theorem finiteInputBound (a : (i : Fin n) → Sec G (e i)) : ∃ L : ℝ, Within L a := by
  classical
  refine ⟨∑ i, ∑ b : Toon G (e i), ‖coord b (a i)‖, ?_⟩
  intro i b
  exact (Finset.single_le_sum (fun c _ => norm_nonneg (coord c (a i))) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun j : Fin n => ∑ c : Toon G (e j), ‖coord c (a j)‖)
      (fun j _ => Finset.sum_nonneg (fun c _ => norm_nonneg (coord c (a j)))) (Finset.mem_univ i))

variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)

theorem coordinate {n : ℕ} (hn : 0 < n) (e : Fin n → ℕ) (h q : ℕ) {K : Set (Points n)}
    (hK : IsCompact K) (hx : K ⊆ conf n) (a : (i : Fin n) → Sec g.core (e i)) (l : Toon g.core h)
    (incomes : ∀ p : ℕ, 1 ≤ p → ∀ B : ℝ, 0 < B →
      AppointedTwoFiledPublicRows.UnselectedIncome.{u,v} g hg periods strict e h p K B) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ o : E4, ∀ x ∈ K,
      ‖coord l (show Sec g.core h from (AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods strict)
        (N g hg) (Q.{u} g hg)).wilsonOPE r h (fun i => ⟨e i,a i⟩) o x) -
        (∑ j ∈ Finset.range (q+1), (heat.{u} g hg periods strict r : ℂ)^j *
          coeff j (filedSeries (N g hg) x a l))‖ ≤
        D * (heat.{u} g hg periods strict r)^(q+1) := by
  obtain ⟨L,hL⟩ := finiteInputBound a
  obtain ⟨D,hD,paid⟩ := AppointedTwoFiledPublicRows.onUnselectedIncomes.{u,v} g hg periods strict
    hn e h q hK hx L incomes
  refine ⟨D,hD,?_⟩
  filter_upwards [paid] with r hr
  intro o x hx₀
  have original := hr o x hx₀ a hL l
  have sub (b c : Sec g.core h) : coord l (b-c) = coord l b - coord l c := by
    simp [coord]
  rw [sub, prescribed (N g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching] at original
  simpa only [YM.FVA2.GradedFar.crop_eq, heat, ElectedMeasurement.clock, V, N, Q] using original

end
end YM.FVA2.GradedFar.AppointedRaisedNumerator

