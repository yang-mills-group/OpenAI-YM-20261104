import YM.Integration.WilsonOriginalPublicReflectedGrid

/-! The time translation between three successive entries in the uncentered
reflected experiment uses the very same original Wilson probability measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicReflectedSlide
open Function Set MeasureTheory Lattice RG Wilson Source Labels Cells
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Therm
open WilsonOriginalPublicReflectedGrid
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {K N p : ℕ}
local notation "X" k:max => Config G (R.family.side k p)
local notation "H" => R.family.path

theorem heard (live : K ≤ N) (P : X K → ℂ) (hP : Envelope P) :
    (∫ U, P U ∂scene (H) N p K) = Wilson.moment (R.family.beta N p) (backTo (H) N p live P) := by
  calc
    _ = ∫ U,backTo (H) N p live P U ∂scene (H) N p N := (retro R.makes.wilson live le_rfl P hP).symm
    _ = _ := by rw [WilsonPositionOriginalDiagnosticReflected.same]; rfl

theorem invariant (live : K ≤ N) (s : Signed) (a : Site (R.family.side K p))
    (P : X K → ℂ) (hp : Envelope P) :
    (∫ U,P (pull s a U) ∂scene (H) N p K) = ∫ U,P U ∂scene (H) N p K := by
  let B := backTo (H) N p live P
  have hm := hp.comp_env (continuous_pull s a).measurable
  change (∫ U,(P ∘ pull s a) U ∂scene (H) N p K) = _
  refine (heard R live (P ∘ pull s a) hm).trans (Eq.trans ?_ (heard R live P hp).symm)
  have zero : anchor R.family.S p (le_refl K) a = a := by
    unfold anchor Ratio.embed Schedule.toDepth
    simp only [tsub_self,Schedule.steps]
    rw [show ((1 : Side).val : ℕ) = 1 from rfl,one_smul,wrap_lift]
  have turns := backTo_orient (H) N p (le_refl K) live a s hp
  rw [zero] at turns
  rw [turns]
  exact moment_pull _ _ _ B ((backTo_env (H) N p live hp).integrableC _)

def shifted {n : Side} (a : Site n) (P : Config G n → ℂ) := P ∘ pull 1 a

/-- A microscopic time step and a translated profile give the neighboring
cross entry exactly, at arbitrary cutoffs and at every admitted K. -/
theorem neighbors (live : K ≤ N) (s : Signed)
    (seam a h : Site (R.family.side K p)) (anti : s.act h = -h)
    (P : X K → ℂ) (hp : Envelope P) :
    pairing R K N p s seam (shifted (a+h) P) (shifted (a+h) P) =
      pairing R K N p s seam (shifted a P) (shifted (a+h+h) P) := by
  let F (U : X K) := P (pull 1 a U) * star (P (pull 1 (a+h+h) (pull s seam U)))
  have env : Envelope F :=
    (hp.comp_env (continuous_pull 1 a).measurable).mulC
      (((hp.comp_env (continuous_pull 1 (a+h+h)).measurable).comp_env (continuous_pull s seam).measurable).starC)
  have equiv (U : X K) :
      shifted (a+h) P U * star (shifted (a+h) P (pull s seam U)) = F (pull 1 h U) := by
    have pos : pull 1 a (pull 1 h U) = pull 1 (a+h) U := by simp [pull_pull,affine]
    have neg : pull 1 (a+h+h) (pull s seam (pull 1 h U)) = pull 1 (a+h) (pull s seam U) := by
      simp [pull_pull,affine,Signed.act_add,anti]
      congr 1; abel
    simp only [F,pos,neg,shifted,Function.comp_apply]
  unfold pairing
  simp_rw [equiv]
  exact invariant R live 1 h F env

/-- Spatial translations of a whole packet preserve its actual
uncentered squared norm. -/
theorem spatial (live : K ≤ N) (s : Signed)
    (seam h : Site (R.family.side K p)) (fixed : s.act h = h)
    (P : X K → ℂ) (hp : Envelope P) :
    pairing R K N p s seam (shifted h P) (shifted h P) =
      pairing R K N p s seam P P := by
  let F (U : X K) := P U * star (P (pull s seam U))
  have env : Envelope F := hp.mulC ((hp.comp_env (continuous_pull s seam).measurable).starC)
  have slide (U : X K) : pull s seam (pull 1 h U) = pull 1 h (pull s seam U) := by
    simp [pull_pull,affine,fixed,add_comm]
  have equiv (U : X K) :
      shifted h P U * star (shifted h P (pull s seam U)) = F (pull 1 h U) := by simp [F,shifted,slide]
  unfold pairing
  simp_rw [equiv]
  exact invariant R live 1 h F env

end YM.Integration.WilsonOriginalPublicReflectedSlide

