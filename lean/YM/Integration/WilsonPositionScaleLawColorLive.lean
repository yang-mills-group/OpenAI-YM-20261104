import YM.Integration.WilsonPositionScaleLawColorReading
import YM.Integration.WilsonPositionScaleLawColorNative
import YM.Integration.WilsonPositionScaleLawGuardNest

/-! A fixed positive margin on one actual grade-six pupil at both physical
radii passes to the unique lower field of each nominated candidate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorLive
open Function Filter Set Spec Table Extraction OPE Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Stab XSpace.Normalize MS MS.Land FVA2 FVA2.Dframe FVA2.Position.OpenAxis
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPhysicalPositionBornCandidates (possible)
open WilsonPhysicalPositionBornTransition (present)
open WilsonPositionScaleLawColorReading (reader Bill)
open WilsonPositionThermometerGradedSource (source)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawCompactNative (positive)
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactBranch
open WilsonPositionScaleLawColorAtHome (Quote)
open WilsonPositionPrescribedFormalTest (raw)
open scoped Topology Classical
variable {G : Gauge} {d : ℕ} {I : Type*} {l : Filter I} [NeBot l]
private abbrev Field (C : Family G) (d : ℕ) := (Bel C.book).Field d

def Original {C : Family G} (z : Fin 3 → G.Color) (s : Rose.Badge) (v : I → Field C 6)
    (l : Filter I) : Prop :=
  ∃ margin : ℝ, 0 < margin ∧ ∀ᶠ i in l,
    -(reader C z (source C s 0)).re + margin ≤ (reader C z (v i)).re

theorem paid (C : Family G) (z : Fin 3 → G.Color) (s : Rose.Badge) (h : 6 ≤ d)
    (a : MoveSpace G d) (v : I → Field C 6) (Y : I → Field C d)
    (seated : ∀ᶠ i in l, (scheme C.labels).rise h (v i) = Y i)
    (approach : Tendsto Y l (𝓝 (present (C:=C) (field a)
      ((scheme C.labels).rise h (source C s 0)))))
    (signed : Original z s v l) : Bill C z s h a := by
  obtain ⟨u,voted⟩ := (WilsonPositionScaleLawColorNative.native C a).lower h (source C s 0)
  obtain ⟨back,undo⟩ := LinearMap.exists_leftInverse_of_injective (K:=ℂ)
    ((scheme C.labels).rise h) (LinearMap.ker_eq_bot.mpr (WilsonPositionScaleLawGuardNest.faithful (C:=C) h))
  have retract (w : Field C 6) : back ((scheme C.labels).rise h w) = w := DFunLike.congr_fun undo w
  have returning : Tendsto (fun i => back (Y i)) l (𝓝 u) := by
    have ok := back.continuous_of_finiteDimensional.continuousAt.tendsto.comp approach
    rw [←voted,retract] at ok
    exact ok
  have into : Tendsto v l (𝓝 u) := returning.congr' (seated.mono (fun i eq => by
    change back (Y i) = v i
    rw [← eq,retract]))
  have measured := ((Complex.continuous_re.comp (reader C z).continuous_of_finiteDimensional).continuousAt.tendsto).comp into
  obtain ⟨margin,pos,bought⟩ := signed
  have lower : -(reader C z (source C s 0)).re + margin ≤ (reader C z u).re :=
    ge_of_tendsto measured bought
  exact ⟨u,voted,by linarith⟩

variable {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S)
    (J : ℝ → tower S) (lead : Leading F J)
include lead in
theorem reporter [RangeSpec] (z : Fin 3 → G.Color) (s : Rose.Badge) (h : 6 ≤ d)
    (a : MoveSpace G d) (dates : I → ℝ × Ratio) (atHome : Tendsto dates l sweep)
    (approach : Tendsto (fun i => change J d (dates i).1 (dates i).2.val (positive (dates i).2)
      ((scheme C.labels).rise h (source C s 0))) l
      (𝓝 (present (C:=C) (field a) ((scheme C.labels).rise h (source C s 0)))))
    (signed : Original z s
      (fun i => change J 6 (dates i).1 (dates i).2.val (positive (dates i).2) (source C s 0)) l) :
    Bill C z s h a := by
  apply paid C z s h a _ _ _ approach signed
  exact (atHome.eventually (WilsonPositionScaleLawGuardNest.natural F J lead h)).mono
    (fun i same => (same (source C s 0)).symm)

end YM.Integration.WilsonPositionScaleLawColorLive
end
