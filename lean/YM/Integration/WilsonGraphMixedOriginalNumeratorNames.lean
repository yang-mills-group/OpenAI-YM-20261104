import YM.Integration.WilsonGraphMixedFarShapeJets
import YM.Integration.WilsonGraphCenteredFarReplacement
import YM.GradedFar.Physical.Contours
import YM.GradedFar.Elected.Voters

/-! The all-r near and far numerator on the separated compact of the original correlation publication. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedMixedCompact

open Function Filter Real Set Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow WilsonGraphPublishedShapeEstimate
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev T := YangMills.hierarchy (g := g) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.P
private abbrev H := Elected.Hframe (N g hg) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.J
private abbrev Cvt := _root_.IssuedBridge.PostedAppointedConversion.filed (N g hg) (Q.{u} g hg).MS
  (Q.{u} g hg).matching (Teller.logNu 1)
private abbrev t := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)

variable {n m : ℕ}

abbrev observed (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    (r s : ℝ) (phase : Option (T.{u} g hg periods strict).Character) (o : Spacetime)
    (z : YM.Points n × YM.Points m) : ℂ :=
  Physical.Y0 (V.{u} g hg periods strict).pupil.last (H.{u} g hg periods strict)
    (fun i : Fin n => w (Fin.castAdd m i)) (fun i : Fin m => w (Fin.natAdd n i))
    (r,s) (phase,o) z.1 z.2 (fun i => a (Fin.castAdd m i)) (fun i => a (Fin.natAdd n i))

theorem names (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    {r : ℝ} (hr : 0 < r) (s : ℝ) (phase : Option (T.{u} g hg periods strict).Character)
    (o : Spacetime) (z : YM.Points n × YM.Points m) (hz : placement s z ∈ YM.conf (n+m)) :
    (T.{u} g hg periods strict).correlation phase
        (fun i => ⟨w i,ElectedMeasurement.frame (V.{u} g hg periods strict) (N g hg) r (w i) (a i)⟩)
        (WithLp.toLp 2 fun i => o+r • placement s z i) =
      observed.{u} g hg periods strict w a r s phase o z := by
  let P := V.{u} g hg periods strict
  let J := H.{u} g hg periods strict
  let sites : YM.Points (n+m) := WithLp.toLp 2 fun i => o+r • placement s z i
  let tags : Fin (n+m) → (YangMills.hierarchy (g := g) P.pupil.last P.pupil.P).Tag :=
    fun i => ⟨w i,ElectedMeasurement.frame P (N g hg) r (w i) (a i)⟩
  let word := fun i : Fin (n+m) => quoteTag (S := P.pupil.S) (tags i)
  let e : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  have safe : sites ∈ YM.conf (n+m) := ElectedMeasurement.centerSeparated hr o (placement s z) hz
  have chart : beside (Physical.atPos r o z.1) (Physical.atPos (r*exp s) o z.2) = sites.ofLp ∘ e := by
    funext i
    rcases i with i | i
    · change o+r • z.1 i = o+r • forest z.1 (squeeze (-s) z.2) (Fin.castAdd m i)
      rw [forest_left]
    · change o+(r*exp s) • z.2 i = o+r • forest z.1 (squeeze (-s) z.2) (Fin.natAdd n i)
      rw [forest_right]
      simp [squeeze,PiLp.smul_apply,← mul_smul]
  have fields : beside
      (Orbits.names (Physical.here J r (d := fun i : Fin n => w (Fin.castAdd m i)) (fun i => a (Fin.castAdd m i))))
      (Orbits.names (Physical.here J r (d := fun i : Fin m => w (Fin.natAdd n i)) (fun i => a (Fin.natAdd n i)))) =
      word ∘ e := by
    funext i
    rcases i with i | i <;> rfl
  let enrolled := beside
    (Orbits.names (Physical.here J r (d := fun i : Fin n => w (Fin.castAdd m i)) (fun i => a (Fin.castAdd m i))))
    (Orbits.names (Physical.here J r (d := fun i : Fin m => w (Fin.natAdd n i)) (fun i => a (Fin.natAdd n i))))
  have positions := congrArg (fun y => observe (spectator P.pupil.last phase) y enrolled) chart
  have letters := congrArg (fun b => observe (spectator P.pupil.last phase) (sites.ofLp ∘ e) b) fields
  have perm := perm_observe (spectator P.pupil.last phase) (spectate P.pupil.last phase).laws.toSymmetric e word safe
  have origin := named_fin (spectator P.pupil.last phase) (spectate P.pupil.last phase).laws.toSymmetric word safe
  unfold observed
  rw [Physical.Y0_value,whole_observed]
  exact ((positions.trans letters).trans (perm.trans origin)).symm

end YM.FVA2.GradedFar.AppointedMixedCompact
end

