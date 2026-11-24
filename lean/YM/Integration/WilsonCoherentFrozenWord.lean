import YM.Integration.WilsonCoherentInheritedLamps

/-! A matrix extension of the original Wilson curvature slot. Frozen links
may be any elements of the compact group. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentFrozenWord
open Function Lattice Wilson RG
open scoped Matrix.Norms.Frobenius ContDiff

variable {G : Gauge}

def word (B : Edge Cover → G.Mat) (x : Cover) : Walk → G.Mat
  | [] => 1
  | s :: w => (if s.neg then star (B (s.used x)) else B (s.used x)) *
    word B (x+s.vec) w

theorem original (U : CoverConfig G) (x : Cover) (w : Walk) :
    word (fun e => G.mat (U e)) x w = G.mat (travel U x w) := by
  induction w generalizing x with
  | nil => simp [word,travel]
  | cons s w ih =>
    simp only [word,travel,G.mat_mul,ih]
    unfold Step.read
    split <;> simp [G.mat_inv]

def slot (B : Edge Cover → G.Mat) (s : RG.Slot) : G.Color :=
  let L := word B 0 s.walk
  let P := word B s.offset (square s.plaq.val.1 s.plaq.val.2)
  let V := L * P * star L
  G.projectColor ((1/2:ℝ) • (V-star V))

theorem observed (U : CoverConfig G) (s : RG.Slot) :
    slot (fun e => G.mat (U e)) s = s.eval U := by
  rw [Slot.eval,←G.curvature_conjugate]
  simp only [slot,original,faceValue,Gauge.curvature,G.mat_mul,G.mat_inv]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {B : E → Edge Cover → G.Mat}
theorem word_smooth (h : ∀ e, ContDiff ℝ ω (fun x => B x e)) (y : Cover) (w : Walk) :
    ContDiff ℝ ω (fun x => word (B x) y w) := by
  induction w generalizing y with
  | nil => exact contDiff_const
  | cons s w ih =>
    simp only [word]
    split
    · exact ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (h _)).mul (ih _)
    · exact (h _).mul (ih _)

theorem slot_smooth (h : ∀ e, ContDiff ℝ ω (fun x => B x e)) (s : RG.Slot) :
    ContDiff ℝ ω (fun x => slot (B x) s) := by
  let L := fun x => word (B x) 0 s.walk
  let P := fun x => word (B x) s.offset (square s.plaq.val.1 s.plaq.val.2)
  let V := fun x => L x * P x * star (L x)
  have lh : ContDiff ℝ ω L := word_smooth h _ _
  have ph : ContDiff ℝ ω P := word_smooth h _ _
  have vh : ContDiff ℝ ω V := (lh.mul ph).mul ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp lh)
  exact G.projectColor.toContinuousLinearMap.contDiff.comp
    ((contDiff_const (c:=(1/2:ℝ))).smul (vh.sub ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp vh)))

end YM.Integration.WilsonCoherentFrozenWord
