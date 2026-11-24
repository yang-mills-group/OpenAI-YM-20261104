import YM.Integration.WilsonPhysicalHistoryPositiveIncome

/-! The normalized original Wilson conditional in an entire physical cutoff
interval, including nonexpansion of a signed local error before summation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryPositiveTower
open Function Filter Finset Set MeasureTheory Lattice Wilson RG OPE OPE.Therm Push.GridApprox
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonReportForwardTransfer
open scoped Classical ENNReal BigOperators
variable {G : Gauge}

private theorem tower (A : History G) (N per : ℕ) {k j t : ℕ} (kj : k ≤ j) (jt : j ≤ t)
    (X : Config G (A.S.side t per)→ℂ) :
    pushTo A N per kj (pushTo A N per jt X) = pushTo A N per (kj.trans jt) X := by
  induction t,jt using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
      rw [pushTo_next A N per ht, pushTo_next A N per (kj.trans ht)]
      exact ih _

private theorem undress (R : Run G) {N per j t : ℕ} (jt : j ≤ t) (top : t ≤ N)
    (X : Config G (R.family.side t per)→ℂ) :
    weighted (C:=R.family) (N:=N) (exterior (C:=R.family) (N:=N) jt X) =
      pushTo R.family.path N per jt (weighted (C:=R.family) (N:=N) X) := by
  funext V
  unfold weighted exterior
  have pos := dose_positive R.makes.wilson (jt.trans top) V
  have nz : (↑(dose (H:=R.family.path) (p:=per) j V N) : ℂ) ≠ 0 := by exact_mod_cast pos.ne'
  field_simp
  rfl

/-- True tower for the physical density-normalized finite-volume transfer.
There is no restriction on the number of intervening steps or on the sign
of the whole mixed source. -/
theorem cascade (R : Run G) {N per k j t : ℕ} (kj : k ≤ j) (jt : j ≤ t) (top : t ≤ N)
    (X : Config G (R.family.side t per)→ℂ) :
    exterior (C:=R.family) (N:=N) kj (exterior (C:=R.family) (N:=N) jt X) =
      exterior (C:=R.family) (N:=N) (kj.trans jt) X := by
  funext V
  change pushTo R.family.path N per kj (weighted (C:=R.family) (N:=N) (exterior (C:=R.family) (N:=N) jt X)) V / _ = _
  rw [undress R jt top, tower R.family.path N per kj jt]
  rfl

private theorem admissible {C : Family G} (hC : C.Makes) {N per j : ℕ} (top : j ≤ N)
    (X : Config G (C.side j per)→ℂ) :
    Integrable X (scene C.path N per j) ↔
      Integrable (weighted (C:=C) (N:=N) X) (prior G (C.side j per)) := by
  unfold scene weighted
  rw [integrable_withDensity_iff_integrable_smul' (dose_env (p:=per) hC.wilson top).meas.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (dose_positive hC.wilson top _).le,Complex.real_smul]

private theorem minus {c f : Side} (S : StepData c f) {β : ℝ} (ker : S.IsKernel β G)
    (X Y : Config G f→ℂ) (hX : Integrable X (prior G f)) (hY : Integrable Y (prior G f)) :
    S.push β (fun U=>X U-Y U) = fun V=>S.push β X V-S.push β Y V := by
  funext V
  simp only [StepData.push,smul_sub]
  rw [integral_sub (StepData.push_slice ker V X hX) (StepData.push_slice ker V Y hY)]

/-- Additivity of the actual normalized conditional for signed fields on
the measured probability space at this precise held cutoff and period. -/
theorem next_sub (R : Run G) {N per j : ℕ} (live : j<N)
    (X Y : Config G (R.family.side (j+1) per)→ℂ)
    (hX : Integrable X (scene R.family.path N per (j+1)))
    (hY : Integrable Y (scene R.family.path N per (j+1))) :
    exterior (C:=R.family) (N:=N) j.le_succ (fun U=>X U-Y U) =
      fun V=>exterior (C:=R.family) (N:=N) j.le_succ X V -
        exterior (C:=R.family) (N:=N) j.le_succ Y V := by
  let A := R.family.path
  let S := A.levels.clock.op j per
  let β := A.β N per (j+1)
  let a := weighted (C:=R.family) (N:=N) X
  let b := weighted (C:=R.family) (N:=N) Y
  have wd : weighted (C:=R.family) (N:=N) (fun U=>X U-Y U) = fun U=>a U-b U := by
    funext U; exact mul_sub _ _ _
  have one (Z : Config G (A.S.side (j+1) per)→ℂ) : pushTo A N per j.le_succ Z = S.push β Z :=
    (pushTo_next A N per (le_refl j) Z).trans (pushTo_self A N per _)
  funext V
  unfold exterior
  rw [wd]
  change pushTo A N per j.le_succ (fun U=>a U-b U) V / _ = pushTo A N per j.le_succ a V / _ - pushTo A N per j.le_succ b V / _
  simp only [one]
  rw [minus S (A.levels.transition_mass j per β) a b ((admissible R.makes live X).mp hX) ((admissible R.makes live Y).mp hY)]
  exact sub_div _ _ _

/-- The local Lipschitz constant on the authentic measured marginal is one.
The signed field difference is formed before either the transfer or its norm. -/
theorem next_distance (R : Run G) {N per j : ℕ} (live : j<N)
    (X Y : Config G (R.family.side (j+1) per)→ℂ)
    (hX : Integrable X (scene R.family.path N per (j+1)))
    (hY : Integrable Y (scene R.family.path N per (j+1))) :
    (∫ V, ‖exterior (C:=R.family) (N:=N) j.le_succ X V -
      exterior (C:=R.family) (N:=N) j.le_succ Y V‖ ∂scene R.family.path N per j) ≤
    ∫ U, ‖X U-Y U‖ ∂scene R.family.path N per (j+1) := by
  calc
    _ = (∫ V, ‖exterior (C:=R.family) (N:=N) j.le_succ (fun U=>X U-Y U) V‖ ∂scene R.family.path N per j) :=
      integral_congr_ae (Eventually.of_forall fun V=>congrArg norm (congrFun (next_sub R live X Y hX hY) V).symm)
    _ ≤ _ := (contract (C:=R.family) R.makes j.le_succ live (fun U=>X U-Y U) (hX.sub hY)).2

end YM.Integration.WilsonPhysicalHistoryPositiveTower

