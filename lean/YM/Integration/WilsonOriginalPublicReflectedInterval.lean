import YM.Integration.WilsonOriginalPublicReflectedSlide

/-! Log convexity between two actual aligned time slices of a finite
Wilson trial, before removing either physical regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicReflectedInterval
open Function Set MeasureTheory Lattice RG Wilson Source Labels Cells
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open WilsonOriginalPublicReflectedSlide WilsonOriginalPublicReflectedGrid
open scoped Classical BigOperators

private theorem bounded (a : ℕ → ℝ) (pos : ∀t, 0 ≤ a t) (m : ℕ)
    (mid : ∀t, t+2 ≤ m → a (t+1)^2 ≤ a t * a (t+2)) :
    ∀t, t ≤ m → a t ≤ max (a 0) (a m) := by
  induction m with
  | zero =>
    intro t ht
    obtain rfl : t = 0 := by omega
    simp
  | succ m ih =>
    have prev := ih (fun t ht => mid t (by omega))
    have slot : a m ≤ max (a 0) (a (m+1)) := by
      by_contra! high
      have h0 := (le_max_left (a 0) (a (m+1))).trans_lt high
      have hm := (le_max_right (a 0) (a (m+1))).trans_lt high
      cases m with
      | zero => exact (lt_irrefl _ h0)
      | succ k =>
        have hb := prev k (by omega)
        rw [max_eq_right h0.le] at hb
        have hc := mid k (by omega)
        have hp := (pos 0).trans_lt h0
        have hprod := mul_le_mul_of_nonneg_right hb (pos (k+2))
        have strict := mul_lt_mul_of_pos_left hm hp
        nlinarith
    intro t ht
    rcases Nat.eq_or_lt_of_le ht with eq | lt
    · simpa only [eq] using le_max_right (a 0) (a (m+1))
    · exact (prev t (by omega)).trans (max_le (le_max_left _ _) slot)

variable {G : Gauge} (R : Run G) {K N p : ℕ}
local notation "X" k:max => Config G (R.family.side k p)
local notation "H" => R.family.path

theorem original (live : K ≤ N) (cut : Cut (R.family.side N p))
    (seam x h : Site (R.family.side K p)) (matched : anchor R.family.S p live seam = cut.slide)
    (anti : cut.flip.act h = -h) (r m : ℕ) (P : X K → ℂ) (loc : Interior (window x r) P)
    (far : ∀t ≤ m, ∀j ≤ m, 2*muzzle (H).levels K r <
      separation (x + t • h) (affine cut.flip seam (x + j • h)))
    (half : ∀t ≤ m, window (anchor R.family.S p live (x + t • h))
      (grows (H).levels K r live) ⊆ cut.sector) :
    ∀t ≤ m, ‖pairing R K N p cut.flip seam (shifted (t • h) P) (shifted (t • h) P)‖ ≤
      max (‖pairing R K N p cut.flip seam P P‖)
        (‖pairing R K N p cut.flip seam (shifted (m • h) P) (shifted (m • h) P)‖) := by
  let F (t : ℕ) := shifted (t • h) P
  let row t j := pairing R K N p cut.flip seam (F t) (F j)
  let T (t : ℕ) := backTo (H) N p live (F t)
  let β := R.family.beta N p
  have localF t : Interior (window (x+t • h) r) (F t) := by
    apply loc.unchanged 1 (t • h)
    simpa [affine] using window_affine (r:=r) x (t • h) (1 : Signed)
  have fine t (ht : t ≤ m) : Interior cut.sector (T t) :=
    (OPE.Strobe.locale (A:=H) (N:=N) (p:=p) (x+t • h) r (localF t) live).enlarges (half t ht)
  have exactRow t j (ht : t ≤ m) (hj : j ≤ m) : row t j = Cells.form β cut (T t) (T j) :=
    WilsonOriginalPublicReflectedTrace.original R live cut seam _ _ matched r (localF t) (localF j) (far t ht j hj)
  have convex t (ht : t+2 ≤ m) : ‖row (t+1) (t+1)‖^2 ≤ ‖row t t‖ * ‖row (t+2) (t+2)‖ := by
    have move : row (t+1) (t+1) = row t (t+2) := by
      simpa only [row,F,succ_nsmul] using neighbors R live cut.flip seam (t • h) h anti P (cylinder_env loc)
    rw [move,exactRow t (t+2) (by omega) ht,exactRow t t (by omega) (by omega),exactRow (t+2) (t+2) ht ht]
    have hot : 0 < β := Overlay.beta_positive R.makes.wilson (m:=N) (N:=N) (p:=p) le_rfl
    exact Cells.cauchy (Slice.reflected_positive cut β hot.le) (fine t (by omega)) (fine (t+2) ht)
  have result := bounded (fun t => ‖row t t‖) (fun t => norm_nonneg _) m convex
  simpa [row,F,shifted,Function.comp_def] using result

/-- Direct uncentered Wilson reflection form at the microscopic end. The
path may consist of arbitrary supported differences on the same original
configuration, including stochastic pullbacks from an earlier date. -/
theorem microscopic (cut : Cut (R.family.side N p)) (h : Site (R.family.side N p))
    (anti : cut.flip.act h = -h) (m : ℕ) (P : X N → ℂ) (env : Envelope P)
    (half : ∀t ≤ m, Interior cut.sector (shifted (t • h) P)) :
    ∀t ≤ m, ‖Cells.form (R.family.beta N p) cut (shifted (t • h) P) (shifted (t • h) P)‖ ≤
      max (‖Cells.form (R.family.beta N p) cut P P‖)
        (‖Cells.form (R.family.beta N p) cut (shifted (m • h) P) (shifted (m • h) P)‖) := by
  let β := R.family.beta N p
  let F (t : ℕ) := shifted (t • h) P
  let row (i j : ℕ) := Cells.form β cut (F i) (F j)
  have paid : 0 < β := Overlay.beta_positive R.makes.wilson (m:=N) (N:=N) (p:=p) le_rfl
  have charge (a b : X N → ℂ) : pairing R N N p cut.flip cut.slide a b = Cells.form β cut a b := by
    unfold pairing
    rw [WilsonPositionOriginalDiagnosticReflected.same R N p]
    rfl
  have convex t (ht : t+2 ≤ m) : ‖row (t+1) (t+1)‖^2 ≤ ‖row t t‖ * ‖row (t+2) (t+2)‖ := by
    have turn := neighbors R (N:=N) le_rfl cut.flip cut.slide (t • h) h anti P env
    simp_rw [charge] at turn
    have near : row (t+1) (t+1) = row t (t+2) := by simpa only [F,row,succ_nsmul] using turn
    rw [near]
    exact Cells.cauchy (Slice.reflected_positive cut β paid.le) (half t (by omega)) (half (t+2) ht)
  have control := bounded (fun t => ‖row t t‖) (fun _ => norm_nonneg _) m convex
  intro t ht
  simpa [row,F,shifted,Function.comp_def] using control t ht

end YM.Integration.WilsonOriginalPublicReflectedInterval


