import YM.Integration.WilsonIndependentOccupiedVista

/-! Each physical regulator and placement may choose its own finite subset of
captured atoms. Its choice is held fixed along the entire finite report. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFreshRoster
open Filter RegulatorIR RegulatorIR.Budget RegulatorIR.Ledger RegulatorIR.Ledger.Sky
variable {W ι : Type} {M : W → ℕ} {X Y : Page M → Type} {S : Sky X Y}
variable {T : S.Accounts} {m : ℕ}

def assemble (rows : W → T.Report m) : T.Report m where
  main p := (rows p.bindW).main p
  point p := (rows p.bindW).point p
  step_m f := (rows f.volW).step_m f
  step_p f := (rows f.volW).step_p f
  ceilingM w := (rows w).ceilingM w
  ceilingP w := (rows w).ceilingP w
  same w := (rows w).same w

theorem hearing [∀ p, Fintype (Y p)] (rows : W → T.Report m) (F : Margins Y) (w : W) (e : ℕ) :
    S.vista T (assemble rows) F w e = S.vista T (rows w) F w e := rfl

theorem uniform [Nonempty ι] (report : W → ℕ) {l : Filter ℕ} (bill : W → ι → Prop)
    (each : ∀ select : W → ι, ∀ᶠ t in l, ∀ w, report w = t → bill w (select w)) :
    ∀ᶠ t in l, ∀ w, report w = t → ∀ a, bill w a := by
  classical
  let pick (w : W) := if h : ∃ a, ¬ bill w a then h.choose else Classical.choice ‹Nonempty ι›
  filter_upwards [each pick] with t paid w site a
  by_contra bad
  have h : ∃ a, ¬ bill w a := ⟨a,bad⟩
  exact h.choose_spec (by simpa only [pick, dif_pos h] using paid w site)

end YM.Integration.WilsonIndependentFreshRoster
