import YM.Integration.WilsonPositionProgramTrialRose
import YM.Integration.WilsonOriginalPublicFigurePole

/-! A fixed measured trial on the actual prior. Its measured vectors are frozen
once at each pair of cutoffs and used at every site and on every subword. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialAppointment
open Function Filter Finset PowerSeries Lattice Wilson RG Labels Source XSpace XSpace.Rose
open XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2 FVA2.Register
open PhysicalNext.Repeat.Legato Extra.Histories Pert.Asymptotics
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOriginalMicroscopicGuardedTrial (gap raw)
open WilsonOriginalPublicTrialInput (salary fitted vector)
open WilsonOriginalPublicFigurePole (opening roof material)
open WilsonPositionProgramTrialSurvey (source)
open WilsonPositionProgramTrialRose (roster)
open WilsonMaxwellThermometerKineticCoordinate (printed)
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (d : Fin 3 → ℕ)

structure Commission (K : ℕ) where
  date : Fin 3 → ℕ
  target : ℕ
  tolerance : ℝ
  money : Fin 3 → ℝ
  fields : (i : Fin 3) → ℕ × ℕ → R.family.label (d i)
  before : ∀ i, date i ≤ K
  registered : Indexed R d date target tolerance money fields

variable {K : ℕ} (C : Commission R d K) (N per : ℕ) (live : K < N)
local notation "v" => vector R d C.date K C.target C.tolerance C.money C.fields C.before C.registered N per
local notation "y" => fitted R d C.date K C.target C.tolerance C.money C.fields C.before C.registered N per
local notation "g" => regulatorRun R.family N per K
local notation "dₛ" S:max => (d ∘ Subtype.val : S → ℕ)

def issued : (i : Fin 3) → R.family.label (d i) := v

include live in
theorem withdrawal (o : Fin 3 → Site (R.family.side K per)) (S : Badge) (u : ℕ) (hu : u ≤ K) :
    (∫ U, ‖actualTransport R.family (N:=N) (gap R d N per K o y S) hu U‖
        ∂OPE.Therm.scene R.family.path N per u) ≤
      WilsonOriginalMicroscopicGuardedWallet.invoice R d K (salary R d C.date K C.tolerance C.money) S *
        R.family.path.levels.clock.forcedAllowance K :=
  (WilsonOriginalPublicTrialInput.original R d C.date K C.target C.tolerance C.money C.fields
    C.before C.registered N per live).2.2.1 o S u hu

include live in
theorem opened (S : Badge) (z : S → Cover) (o : Fin 3 → Site (R.family.side K per))
    (placed : ∀ i:S, wrap (R.family.side K per) (z i) = o i) (U : Config G (R.family.side K per)) :
    opening R (dₛ S) (fun i:S => v i) z g U =
      (g:ℂ) ^ roof R (dₛ S) * ∏ i:S, raw R d N per K o y i U := by
  have positive : g ≠ 0 := (inv_pos.mpr (Real.sqrt_pos.mpr
    (Overlay.beta_positive R.makes.wilson live.le))).ne'
  rw [WilsonOriginalPublicFigurePole.field _ _ _ _ _ positive, WilsonOriginalPublicTrialFigure.opened]
  rw [WilsonOriginalPublicTrialFigure.original R d C.date K C.target C.tolerance C.money C.fields
    C.before C.registered N per live Subtype.val o z placed U]

theorem normalized (W : Initialize G) (t : Sample 3) (S : Badge) :
    Bare.normalized (W.tree t.F.p) G (material R (dₛ S) (fun i:S => v i) (t.layout ∘ Subtype.val)
      t.F.p (W.tree t.F.p)) = X ^ roof R (dₛ S) * source R d v W t S :=
  WilsonOriginalPublicFigurePole.filed R (dₛ S) (fun i:S => v i) _ _ _

variable (cap : ∀ i, d i < 7) (Z : WilsonPrescription G) (m : Mesh)

def reading (q : ℕ) (u : ℝ) : ℝ :=
  ∑ e : Fin (q+1), (Deposit m (fun t => coeff (e:ℕ) (b3 (source R d v Z.scheme t)))
    (test Z.criterion)).re * u^(e:ℕ)

def expense (q : ℕ) (u : ℝ) : ℝ :=
  ∑ e : Fin (q+1), (Deposit m (fun t => coeff (e:ℕ) (roster R d cap v Z.scheme Z.store t))
    (test Z.criterion)).re * u^(e:ℕ)

theorem original (q : ℕ) (u : ℝ) :
    reading R d C N per Z m q u - printed Z m q u = expense R d C N per cap Z m q u := by
  unfold reading printed expense
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro e _
  rw [← sub_mul, ← Complex.sub_re, WilsonPositionProgramTrialRose.original R d cap v Z m]

end YM.Integration.WilsonPositionProgramTrialAppointment
end
