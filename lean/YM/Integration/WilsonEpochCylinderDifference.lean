import YM.PertExtension.Normalized

/-! A difference of two normalized inversion coefficients on the same
microscopic torus. Each summand changes one actual cylinder and retains the
other occurrences, the interacting Wilson action, and the common vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochCylinderDifference

open Function Lattice Wilson MeasureTheory PertExtension PertExtension.Orb
open scoped Topology ContDiff Classical

variable {G : Gauge} {n : Side}
private abbrev field := Config G n → ℝ

private theorem plus {f g : field (G := G) (n := n)} (hf : PreTest f)
    (hg : PreTest g) : PreTest (f + g) where
  gauge u hu U := congrArg₂ (· + ·) (hf.gauge u hu U) (hg.gauge u hu U)
  curved := ⟨hf.curved.boundedness.add hg.curved.boundedness, hf.curved.germ.add hg.curved.germ⟩
  continuous := hf.continuous.add hg.continuous

theorem minus {f g : field (G := G) (n := n)} (hf : PreTest f)
    (hg : PreTest g) : PreTest (f - g) where
  gauge u hu U := congrArg₂ (· - ·) (hf.gauge u hu U) (hg.gauge u hu U)
  curved := ⟨hf.curved.boundedness.sub hg.curved.boundedness, hf.curved.germ.sub hg.curved.germ⟩
  continuous := hf.continuous.sub hg.continuous

private theorem expectation_add (ev : Even n.val) {f g : field (G := G) (n := n)}
    (hf : PreTest f) (hg : PreTest g) :
    preExpectation (f + g) = preExpectation f + preExpectation g := by
  funext t
  change preNum (f+g) t / _ = preNum f t / _ + preNum g t / _
  rw [← add_div,preNum_eq _ _ ev (plus hf hg).continuous (plus hf hg).gauge,
    preNum_eq _ _ ev hf.continuous hf.gauge,preNum_eq _ _ ev hg.continuous hg.gauge]
  congr 1
  unfold numerator
  have split : entries (restrictedO (f+g)) t =
      entries (restrictedO f) t + entries (restrictedO g) t := by
    funext V
    exact add_mul _ _ _
  simp only [split,Pi.add_apply]
  exact integral_add (entries_integrable hf.curved.boundedness t)
    (entries_integrable hg.curved.boundedness t)

/-- Signed scalar reads are linear at *every* perturbative order although the
interacting action and its vacuum series are kept in the normalized quotient. -/
theorem coefficient (ev : Even n.val) {f g : field (G := G) (n := n)}
    (hf : PreTest f) (hg : PreTest g) (k : ℕ) :
    diag (restrictedO f) k - diag (restrictedO g) k = diag (restrictedO (f-g)) k := by
  let hδ := minus hf hg
  have h := (before_tree_formula ev (traySpec G) hδ).add
    (before_tree_formula ev (traySpec G) hg)
  rw [← expectation_add ev hδ hg,sub_add_cancel] at h
  have q := congrFun (h.unique (before_tree_formula ev (traySpec G) hf)) k
  change diag (restrictedO (f-g)) k + diag (restrictedO g) k = diag (restrictedO f) k at q
  linarith

variable {ι : Type*} {A : Type*} [CommRing A]

def word (F : ι → A) (l : List ι) := (l.map F).prod

/-- Ordered one-cylinder changes. Positions are occurrences: the same
native field or physical center may appear any number of times. -/
def insertion (F H : ι → A) : List ι → A
  | [] => 0
  | i::l => (F i - H i)*word F l + H i*insertion F H l

theorem telescope (F H : ι → A) (l : List ι) :
    word F l - word H l = insertion F H l := by
  induction l with
  | nil => simp [word,insertion]
  | cons i l ih =>
    change F i*word F l - H i*word H l = (F i-H i)*word F l + H i*insertion F H l
    rw [←ih]
    ring

theorem mixed (ev : Even n.val) (F H : ι → Config G n → ℝ) (l : List ι)
    (hf : PreTest (word F l)) (hh : PreTest (word H l)) (k : ℕ) :
    diag (restrictedO (word F l)) k - diag (restrictedO (word H l)) k =
      diag (restrictedO (insertion F H l)) k := by
  rw [←telescope]
  exact coefficient ev hf hh k

end YM.Integration.WilsonEpochCylinderDifference
end

