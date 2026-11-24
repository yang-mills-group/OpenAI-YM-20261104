import YM.Integration.WilsonIndependentFreshCoverWard
import YM.RegulatorIR.Tape.Resound

/-! A freshly planted group word on a nonbare course satisfies the cover Ward
identity at every subsequent wing. The finite measures on the growing tori
are the original Wilson measures with their entire preceding quiet history. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonIndependentFreshDeviationWard
open RegulatorIR
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding
open Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram
open Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG
open Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Sight
open Gain WilsonIndependentFreshCopyWage
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}
  (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p k m s : ℕ} (B : S.Primitive L p k)
  (Z : (E.part S T B).Report m) (w : W) (bank : S.Supplies T L p k)
  (C : Aug.Amenities S L p k) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))
  (j : ℕ) (hj : j ≤ E.spans w) (hk : 14 ≤ k)

def folded (h : Page E.spans) :=
  fun e r => (S.maps (E.page h)).scroll (Z.main h e r)

include stamp bank C quiet large in
theorem rider (x : ℝ → Horizon G (n (E.page ⟨w,j,hj⟩))) {i : ℕ} (hi : i ≤ p) :
    coeff i (reel (folded T E B Z ⟨w,j,hj⟩) m x) =
    rhymeR (chord (S.maps (E.page ⟨w,j,hj⟩)) (vow (peel x))) (Z.main ⟨w,j,hj⟩) m i := by
  rw [rhyme_tube]
  unfold rhymeR
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro r _
  apply chord_port
  exact WilsonIndependentFreshCopyLimit.cusp_b H T quiet large E B Z w bank C film stamp j hj r _
    (by have hr := mem_antidiagonal.mp hq; omega)

include stamp bank C quiet large hk in
theorem two {x y : ℝ → Horizon G (n (E.page ⟨w,j,hj⟩))}
    (hx : ContDiffAt ℝ ∞ x 0) (hy : ContDiffAt ℝ ∞ y 0) (same : reel_prop x y) :
    Squares p (reel (Z.deviation ⟨w,j,hj⟩) m x) (reel (Z.deviation ⟨w,j,hj⟩) m y) := by
  obtain ⟨_,_,finite,_⟩ := WilsonIndependentFreshQuietReel.issued H T quiet E B Z film stamp
  have full := finite ⟨w,j,hj⟩ x y hx hy same
  have cover : Squares p (reel (folded T E B Z ⟨w,j,hj⟩) m x) (reel (folded T E B Z ⟨w,j,hj⟩) m y) := by
    intro a ha
    rw [rider H T quiet large E B Z w bank C film stamp j hj x ha,
      rider H T quiet large E B Z w bank C film stamp j hj y ha]
    exact WilsonIndependentFreshCoverWard.matched H T quiet large E B Z w bank C film stamp j hj hk
      (world H w (E.age w+j) (absAge E w hj) hx p)
      (world H w (E.age w+j) (absAge E w hj) hy p)
      (fun _ => waveV _ (H.even _) same) ha
  have split u : reel (Z.deviation ⟨w,j,hj⟩) m u =
      reel (Z.point ⟨w,j,hj⟩) m u - reel (folded T E B Z ⟨w,j,hj⟩) m u := by
    rw [show Z.deviation ⟨w,j,hj⟩ = Z.point ⟨w,j,hj⟩ - folded T E B Z ⟨w,j,hj⟩ from rfl]
    unfold reel
    rw [reel_split,map_sub]
  rw [split x,split y]
  apply Squares.sub _ cover
  intro i hi
  rw [full]

variable {J : Flap M → Layer (Foot G) (Foot G)} {V : Flap M → Bride G}
  {c : Flap M → ℝ≥0∞} (A : Azur H J V k L c) (inspiration : Inspires J V S)
include stamp bank C quiet hk A inspiration in
theorem original (wing : Flap E.spans) (i : ℕ) (hi : i ≤ p) :
    (S.sight (E.wing wing)).WayO (Z.deviation wing.prev) i := by
  obtain ⟨w,j,h⟩ := wing
  let wing : Flap E.spans := ⟨w,j,h⟩
  change (S.sight (E.wing wing)).WayO (Z.deviation wing.prev) i
  rw [inspiration.tune]
  refine noble _ (A.invoke _) (m:=m) ?_ ?_ hi
  · intro e _ r he
    have cov := Z.cap_b (fun a => essential H (E.wing a)) wing.prev e
    have tor := Z.cap_o (fun a => essential H (E.wing a)) wing.prev e
    by_contra! exceeds
    apply he
    unfold Sky.Accounts.Report.deviation
    rw [show Z.point _ e r = 0 from Classical.not_not.mp (fun v => (not_le.mpr exceeds) (tor r v)),
      show Z.main _ e r = 0 from Classical.not_not.mp (fun v => (not_le.mpr exceeds) (cov r v)),
      Deck.scroll_zero,sub_self]
    rfl
  intro x y Hx Hy hs
  exact two H T quiet A.run E B Z w bank C film stamp j h.le hk Hx Hy hs
end YM.Integration.WilsonIndependentFreshDeviationWard
