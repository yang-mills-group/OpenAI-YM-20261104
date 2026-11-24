import YM.Integration.WilsonGraphSingletonNearFormal
import YM.OPE.Splitting.Observe
import YM.GradedFar.Continuation.Insert

/-! The actual single near operator can be read at a common grade, with the same elected
    frame, all viewer phases and the original filed coefficient row. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedOneNear

open Function Filter Finset Set Real PowerSeries Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev H := Elected.Hframe (N g hg) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.J

variable {m : ℕ} {d : Fin 1 → ℕ} {e : Fin m → ℕ} {h : ℕ}

theorem framedSeparated {r : ℝ} (hr : 0 < r) (s : ℝ) (o : E4) (x : YM.Points 1)
    (y : YM.Points m) (safe : placement s (x,y) ∈ YM.conf (1+m)) :
    Function.Injective (beside (Physical.atPos r o x) (Physical.atPos (r*Real.exp s) o y)) := by
  let p : YM.Points (1+m) := WithLp.toLp 2 (fun i => o+r • placement s (x,y) i)
  let eqv : Fin 1 ⊕ Fin m ≃ Fin (1+m) := finSumFinEquiv
  have sep : p ∈ YM.conf (1+m) := ElectedMeasurement.centerSeparated hr o _ safe
  have chart : beside (Physical.atPos r o x) (Physical.atPos (r*Real.exp s) o y) = p.ofLp ∘ eqv := by
    funext i
    rcases i with i | i
    · change o+r • x i = o+r • forest x (squeeze (-s) y) (Fin.castAdd m i)
      rw [forest_left]
    · change o+(r*Real.exp s) • y i = o+r • forest x (squeeze (-s) y) (Fin.natAdd 1 i)
      rw [forest_right]
      simp [squeeze,PiLp.smul_apply,←mul_smul]
  rw [chart]
  exact sep.comp eqv.injective

theorem physicalCap (hd : ∀ i, d i ≤ h) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : ℝ) (phase : Viewers (V.{u} g hg periods strict).pupil.last)
      (o : E4) (x : YM.Points 1) (y : YM.Points m), placement s (x,y) ∈ YM.conf (1+m) →
      ∀ (u : Inputs g.core d) (v : Inputs g.core e),
      Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
        d e (r,s) (phase,o) x y u v =
      Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
        (fun _ : Fin 1 => h) e (r,s) (phase,o) x y (installedInputs hd u) v := by
  let P := V.{u} g hg periods strict
  let U := P.pupil.last
  let S := P.pupil.S
  let J := H.{u} g hg periods strict
  filter_upwards [ElectedMeasurement.included P (N g hg) (Q.{u} g hg) (hd 0),
    self_mem_nhdsWithin] with r inc pos
  intro s phase o x y safe u v
  let low := Orbits.names (Physical.here J r u)
  let high := Orbits.names (Physical.here J r (d := fun _ : Fin 1 => h) (installedInputs hd u))
  let far := Orbits.names (Physical.here J r v)
  let mark := beside low far
  let p := low 0
  let q := high 0
  have lowAt : update mark (Sum.inl 0) p = mark := by
    funext i
    by_cases eq : i=Sum.inl 0
    · subst i
      rw [update_self]
      rfl
    · rw [update_of_ne eq]
  have highAt : update mark (Sum.inl 0) q = beside high far := by
    funext i
    rcases i with j|j
    · obtain rfl : j=0 := Subsingleton.elim _ _
      rw [update_self]
      rfl
    · rw [update_of_ne (by simp)]
      rfl
  have included : U.sector.derivatives.rise (hd 0) (S.project (d 0) p.2) = S.project h q.2 := by
    change U.sector.derivatives.rise (hd 0) (S.project _ (S.representative _ (J r (d 0) (u 0)))) =
      S.project _ (S.representative _ (J r h (XSpace.Normalize.up (hd 0) (u 0))))
    rw [S.rep,S.rep]
    exact (inc (u 0)).symm
  have paid := observe_replace (spectator U phase) mark (p := p) (v' := q)
    (spectate U phase).laws.toSymmetric (spectate_respects U phase) (spectate_ready U phase)
    (framedSeparated pos s o x y safe) (Sum.inl 0) (hd 0) included
  rw [lowAt,highAt] at paid
  rw [Physical.Y0_value,Physical.Y0_value,whole_observed,whole_observed]
  exact paid.symm

theorem formalCap (hd : ∀ i, d i ≤ h) (he : ∀ i, e i ≤ h) (s : ℝ)
    (x : YM.Points 1) (u : Inputs g.core d) (y : YM.Points m) (v : Inputs g.core e)
    (safe : placement s (x,y) ∈ YM.conf (1+m)) :
    Continuation.row (N g hg) x u y v s =
      Continuation.row (N g hg) (d := fun _ : Fin 1 => h) x (installedInputs hd u) y v s := by
  ext j
  rw [Continuation.coeff_row (Q.{0} g hg).matching x u y v s hd he safe j,
      Continuation.coeff_row (Q.{0} g hg).matching x (d := fun _ : Fin 1 => h)
        (installedInputs hd u) y v s (fun _ => le_rfl) he safe j]
  rfl

end YM.FVA2.GradedFar.AppointedOneNear
end

