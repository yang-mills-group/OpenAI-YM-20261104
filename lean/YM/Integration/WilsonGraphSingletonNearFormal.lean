import YM.Integration.WilsonGraphMixedCompactNumerator
import YM.Integration.WilsonGraphSingletonNearReanchoring
import YM.Integration.WilsonGraphAppointedCropDetermination

/-! Simultaneous translation of the elected formal numerator, through every order at its original grades. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOneNear

open Function Filter Finset Set Real PowerSeries Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow AppointedMixedCompact WilsonGraphPublishedShapeEstimate
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (N g hg) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.J
private abbrev heat := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)

variable {m : ℕ}

theorem stage (s : ℝ) (x : YM.Points 1) (y : YM.Points m) (i : Fin (1+m)) :
    placement s (x,y) i = x 0 + placement s (0,exterior s x y) i := by
  induction i using Fin.addCases with
  | left j =>
    change forest x (squeeze (-s) y) (Fin.castAdd m j) =
      x 0 + forest (0 : YM.Points 1) (squeeze (-s) (exterior s x y)) (Fin.castAdd m j)
    rw [forest_left,forest_left]
    obtain rfl : j=0 := Subsingleton.elim _ _
    simp
  | right j =>
    change forest x (squeeze (-s) y) (Fin.natAdd 1 j) =
      x 0 + forest (0 : YM.Points 1) (squeeze (-s) (exterior s x y)) (Fin.natAdd 1 j)
    rw [forest_right,forest_right]
    simp only [squeeze,neg_neg,PiLp.smul_apply]
    change Real.exp s • y j = x 0 + Real.exp s • (y j - Real.exp (-s) • x 0)
    rw [smul_sub,smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
    abel

theorem stageSeparated (s : ℝ) (x : YM.Points 1) (y : YM.Points m)
    (safe : placement s (0,exterior s x y) ∈ YM.conf (1+m)) :
    placement s (x,y) ∈ YM.conf (1+m) := by
  intro i j eq
  exact safe (add_left_cancel ((stage s x y i).symm.trans (eq.trans (stage s x y j))))

include periods strict in
/-- At each fixed separated pair, two true all-order prices and the identical physical numerator
    determine the original full series at both placements. -/
theorem formal (w : Fin (1+m) → ℕ) (a : (i : Fin (1+m)) → Sec g.core (w i))
    (s : ℝ) (x : YM.Points 1) (y : YM.Points m)
    (safe : placement s (0,exterior s x y) ∈ YM.conf (1+m)) :
    series g hg w a s (x,y) = series g hg w a s (0,exterior s x y) := by
  let z := (x,y)
  let b : YM.Points 1 × YM.Points m := (0,exterior s x y)
  let K : Set (YM.Points (1+m)) := insert (placement s z) {placement s b}
  have compact : IsCompact K := isCompact_singleton.insert _
  have inside : K ⊆ YM.conf (1+m) := by
    intro t ht
    rcases Set.mem_insert_iff.mp ht with h|h
    · subst t
      exact stageSeparated s x y safe
    · rw [Set.mem_singleton_iff] at h
      subst t
      exact safe
  have here : placement s z ∈ K := Set.mem_insert _ _
  have there : placement s b ∈ K := Set.mem_insert_of_mem _ rfl
  let cap := Finset.univ.sup w
  have within : ∀ i, w i ≤ cap := fun i => Finset.le_sup (Finset.mem_univ i)
  let M := ∏ i, sectorMass (B := _root_.IssuedMaxwell.Reports.B g) (a i)
  let θ := heat.{0} g hg periods strict
  have positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < θ r :=
    ElectedMeasurement.positive (V.{0} g hg periods strict) (N g hg) (Q.{0} g hg)
  have vanishes : Tendsto θ (𝓝[>] 0) (𝓝 0) :=
    ((V.{0} g hg periods strict).certificate (Q.{0} g hg)).calendar.clock.conforms
      (_root_.IssuedMaxwell.ElectedPrescription.simple g hg)
  apply AppointedCropDetermination.determined θ positive vanishes
  intro p
  obtain ⟨D,_,event⟩ := AppointedMixedCompact.onCompact.{0} g hg periods strict cap p compact inside
  refine ⟨2*(D*M),?_⟩
  filter_upwards [event] with r paid
  let Y := AppointedMixedCompact.observed.{0} g hg periods strict w a r s none 0 z
  let A := crop p (θ r) (series g hg w a s z)
  let B := crop p (θ r) (series g hg w a s b)
  have first : ‖Y-A‖ ≤ D*M*|θ r|^(p+1) := paid s w within a none 0 z here
  have same : Y = AppointedMixedCompact.observed.{0} g hg periods strict w a r s none (0+r • x 0) b :=
    physical (V.{0} g hg periods strict).pupil.last (H.{0} g hg periods strict) (r,s)
      none 0 x y (fun i => a (Fin.castAdd m i)) (fun i => a (Fin.natAdd 1 i))
  have last := paid s w within a none (0+r • x 0) b there
  rw [←same] at last
  calc ‖A-B‖ ≤ ‖A-Y‖+‖Y-B‖ := norm_sub_le_norm_sub_add_norm_sub A Y B
       _ ≤ D*M*|θ r|^(p+1)+D*M*|θ r|^(p+1) := add_le_add ((norm_sub_rev A Y).le.trans first) last
       _ = 2*(D*M)*|θ r|^(p+1) := by ring

end YM.FVA2.GradedFar.AppointedOneNear
end

