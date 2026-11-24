import YM.WilsonCoeffUV.Reclosure.Paths.Ebase
import YM.PertExtension.Uniform

/-! Real finite-torus actions underlying the independent graded packets.
Each packet retains its actual atom sequence, all lattice translates and
the original signed average. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedPeriodAction

open Filter Function Matrix Lattice Laurent Bloch Wilson RG Precision Exterior Stationary PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FreeResolvent
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {s A : ℝ} (n : Side)

def action (a : PrismA G) (U : Config G n) : ℝ :=
  Patch.average fun h : Signed => uncut a.cells (pull h 0 U)

def rendered (Z : SeriesA G) (g : ℝ) (U : Config G n) : ℝ :=
  (Z.map fun a => g^(a.grade-a.rise) * action n a U).sum

theorem links (a : PrismA G) (w : TreeVars G n) :
    action n a (mantle w) = turnSeries a.cells w := by
  unfold action turnSeries
  rw [Mosaic.mantle_input]

theorem shell (a : PrismA G) :
    flash (Mosaic.surf a n) =
      X^a.grade * flash (sprig (turnSeries a.cells (m:=n)) (a.rise+2)) := by
  apply PowerSeries.ext
  intro j
  rw [coeff_X_pow_mul',Blue.flash,coeff_mk]
  unfold Mosaic.surf
  split
  · simp only [Blue.flash,coeff_mk]
  simp [totalR]

theorem packet (hs : 0 < s) (a : PrismA G) (ha : Commission a.cells s A a.grade) :
    X^2 * flash (Mosaic.surf a n) =
      X^(a.grade-a.rise) * jet (turnSeries a.cells (m:=n)) := by
  let f := turnSeries a.cells (m:=n)
  have hg : Green f := (turns_analytic a.cells hs ha.toll).contDiffAt
  have ht : X^(a.rise+2) * flash (sprig f (a.rise+2)) = jet f := by
    apply moves
    intro k hk
    rw [jet_apply,show rye f k = 0 from ?_,map_zero]
    funext x
    unfold rye
    rw [(rays_jet hg.analyticAt (a.rise+2)).1 (turns_low a.cells hs ha.toll) k hk]
    simp
  rw [shell, ← show X^(a.rise+2) * flash (sprig f (a.rise+2)) =
      jet (turnSeries a.cells (m:=n)) from ht]
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
  congr 2
  have h := a.rankA
  omega

def formal (Z : SeriesA G) : Ink (Woods G n) :=
  (Z.map fun a => X^(a.grade-a.rise) * jet (turnSeries a.cells (m:=n))).sum

theorem packets (hs : 0 < s) (Z : SeriesA G) (hZ : Draw Z s A) :
    X^2 * flash (sands Z n) = formal n Z := by
  induction Z with
  | nil =>
    have h : flash (sands ([] : SeriesA G) n) = 0 := by
      ext1 j
      simp [sands,Blue.flash,totalR]
    rw [h,mul_zero]
    rfl
  | cons a Z ih =>
    have ha : shellK 2 (Mosaic.surf a n) := by
      intro e t ht
      unfold Mosaic.surf
      split
      · unfold sprig
        apply shine_dark
        have hh := a.rankA
        omega
      rfl
    rw [show sands (a::Z) n = Mosaic.surf a n + sands Z n from rfl,
      flash_add (finite_shell ha) (finite_shell (sand_span Z n)),mul_add,
      packet n hs a (hZ.2 a List.mem_cons_self),
      ih ⟨hZ.1,fun b hb => hZ.2 b (List.mem_cons_of_mem a hb)⟩]
    rfl

theorem radial_packet (hs : 0 < s) (a : PrismA G) (ha : Commission a.cells s A a.grade)
    (w : TreeVars G n) (j : ℕ) :
    MvPolynomial.eval w (coeff j (X^2 * flash (Mosaic.surf a n))) =
      if a.grade-a.rise ≤ j then
        ((j-(a.grade-a.rise)).factorial : ℝ)⁻¹ *
        iteratedDeriv (j-(a.grade-a.rise)) (fun g : ℝ => action n a (mantle (g • w))) 0
      else 0 := by
  rw [packet n hs a ha,coeff_X_pow_mul']
  split_ifs
  · rw [rayon]
    simp_rw [links]
    exact PertExtension.Series.Radial.homogeneous_derivative _ w _
      ((turns_analytic a.cells hs ha.toll).contDiffAt.of_le le_top)
  exact map_zero _

end YM.Integration.FundedPeriodAction
