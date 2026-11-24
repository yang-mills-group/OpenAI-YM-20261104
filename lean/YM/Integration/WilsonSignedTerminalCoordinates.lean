import YM.Integration.WilsonCutoffDiscrepancyPrice
import YM.Work.D01
import YM.FullVolume.Fire

/-! The actual terminal inverse has a regulator-dependent absolute column
bill. Charge it in the same ultraviolet envelope as the signed field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSignedTerminalCoordinates
open Filter Lattice Wilson RG Labels Extra.Histories MergeProof Next.Extract
open WilsonCutoffDiscrepancyPrice
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G)

def column (N : ℕ) := Real.exp (Work.D01.columnLogs C.path.levels N)
def joint (E : ℕ → ℝ) (N : ℕ) := column C N*E N

theorem slow (E : ℕ → ℝ) (hE : FullVolume.Sluggish C (fun i => E i.1)) :
    FullVolume.Sluggish C (fun i => joint C E i.1) := by
  have h : FullVolume.Sluggish C (fun i => column C i.1) := by
    intro ε hε
    apply FullVolume.late.mpr
    filter_upwards [Work.D01.columnLogs_le C.path.levels ε hε] with N hN p
    change ‖Real.exp _‖ ≤ Real.exp _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr hN
  exact h.mul hE

theorem before (E : ℕ → ℝ) (k N : ℕ) :
    column C N*price C E k N = price C (joint C E) k N := by
  unfold joint price column
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]; ring

theorem terminal (H : C.Makes) (d N p : ℕ) (hr : C.ref d≤N) (v : C.label d) :
    (C.labels.level d).coeffSize ((C.factory d N p).terminal.symm v) ≤
      column C N * (C.labels.level d).coeffSize v := by
  have h := Work.D01.back_budget C H (p:=p) v hr (le_refl N)
  change (C.labels.level d).coeffSize
    (((C.factory d N p).entries N ((C.factory d N p).terminal.symm v)).x) ≤ _ at h
  rw [(H.calibrated d N p hr).bare_coord _] at h
  exact h

private theorem projected_norm {X : Type*} [SeminormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) {a : ℝ} (ha : ‖T‖ ≤ a) (x : X) : ‖x-T x‖ ≤ (1+a)*‖x‖ := by
  calc
    ‖x-T x‖ ≤ ‖x‖+‖T x‖ := norm_sub_le _ _
    _ ≤ ‖x‖+a*‖x‖ := add_le_add_right ((T.le_opNorm x).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg x))) _
    _ = (1+a)*‖x‖ := by ring

theorem projected (H : C.Makes) (d N p : ℕ) (hr : C.ref d≤N)
    (P : C.label d ≃ₗ[ℂ] C.label d) (post : ∀ z, (C.labels.level d).coeffSize (P.symm z) ≤
      2*(C.labels.level d).coeffSize z) (T : CoordMap C d) {A : ℝ} (hA : ‖T‖≤A)
    (x : C.label d) :
    (C.labels.level d).coeffSize (P.symm ((C.factory d N p).terminal.symm (x-T x))) ≤
      (2*(Fintype.card (C.labels.level d).Index:ℝ)*(1+A)*‖x‖)*column C N := by
  let F:=C.labels.level d
  have hx := projected_norm T hA x
  apply (post _).trans
  apply (mul_le_mul_of_nonneg_left (terminal C H d N p hr (x-T x)) zero_le_two).trans
  have hsize := (Size.le_norm F (x-T x)).trans (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _))
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le) zero_le_two).trans_eq
  dsimp only [F,column]
  ring

end YM.Integration.WilsonSignedTerminalCoordinates
