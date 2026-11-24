import YM.Integration.MSFixedRatioGeometry
import YM.FVAAlt2.Rocket.Code
import YM.RegulatorIR.Atlas.Shelves

/-! Native lattice units preserve the original inversion side and every branch. On this
same finite history, both the calibrated kinetic clocks and original atlas budgets are
purchased at any fixed finite order once the fixed block ratio exceeds the native demand. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.MSFixedRatioCalibration
open Lattice RG RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Epoch
open RegulatorIR.Atlas RegulatorIR.Uniform RegulatorIR.Calibration PertExtension.LatticePT
open MSFixedRatioGeometry
open scoped ENNReal NNReal Classical

def lattice (p : Patch) : Circuit history (window p) :=
  { circuit p with
    l := fun w=> (p.L.val:ℝ)^w.downW
    P := fun k=> (side p.L k).val
    l_p := fun _=> pow_pos (by exact_mod_cast p.L.pos) _
    comet := fun w=> by
      have ell := epsilon_pos p.L w.bindW
      apply mul_right_cancel₀ ell.ne'
      have hc := (circuit p).comet w
      change (epsilon p.L w.bindW*(p.L.val:ℝ)^w.downW)*(window p w).val = _ at hc
      calc
        ((p.L.val:ℝ)^w.downW*(window p w).val)*epsilon p.L w.bindW =
          (epsilon p.L w.bindW*(p.L.val:ℝ)^w.downW)*(window p w).val := by ring
        _ = _ := hc }

def marked (p : Patch) := League.stampE (lattice p) (fun _=>0) (fun _=>le_rfl)

/-- The original torus starts at one native lattice unit and ends with eight sites per axis. -/
theorem extent (p : Patch) (k : ℕ) :
    (lattice p).l (Page.opening history k) = 1 ∧ (window p (Page.finallyW history k)).val = 8 ∧
      (lattice p).P k = (side p.L k).val := by
  refine ⟨pow_zero _,?_,rfl⟩
  change 8*p.L.val^(history k-history k)=8
  simp

theorem step (p : Patch) (f : Flap history) : (lattice p).pactP f = p := by cases p; rfl

/-- The original definition of a normalized notebook applies with either reference level. -/
theorem notebooks {G : Gauge} {K : KernelChoices} (p : Patch) (Y : Program K)
    (Z : ∀ p : Patch, p.Branches K G) (c : G.ColorIndex) (D : Choice history) (n : ℕ) :
    ∃ F : Tent history, Notebook (lattice p) Y G Z c D F n :=
  tomorrows (lattice p) Y G Z c D n

/-- These actual native budgets are uniform in the fine history. The sole lower bound on
`p.L` is precisely the original atlas threshold at this smoothing index and order. -/
theorem budgets {G : Gauge} {K : KernelChoices} (p : Patch) (Y : Program K)
    (Z : ∀ p : Patch, p.Branches K G) (n u : ℕ) (h₁ : 3≤u) (h₂ : n+2≤u) (hJ : 5≤p.J)
    (hL : orders G Y n u p.J (1/2) (by norm_num) (by norm_num) ≤ p.L.val) :
    SatisfiesQ G Y (lattice p) Z (marked p) n u (1/2) := by
  refine ⟨fun _=>rfl,?_,h₁,h₂,?_,?_,by norm_num,by norm_num,fun _=>hJ,fun _=>hL⟩
  · constructor <;> exact Poly.standard _ (u:=ENNReal.ofReal (p.L.val:ℝ)) ENNReal.ofReal_ne_top
  · have hp := Poly.standard (marked p).age_f (gf_f G Y Z (p:=n) (u:=u) p)
    apply hp.mono
    intro f
    change glowF G Y Z n u ((lattice p).pactP f) ≤ glowF G Y Z n u p
    rw [step]
  · exact Poly.standard _ (gpage_f G Y (u:=u) p.J)

/-- Apply both original purchases on this family of physical inversion arrays. -/
theorem original {G : Gauge} {K : KernelChoices} (Y : Program K) (Z : ∀ p : Patch, p.Branches K G)
    (j n u : ℕ) (hj : 5≤j) (h₁ : 3≤u) (h₂ : n+2≤u) (c : G.ColorIndex) :
    ∃ L₀ : ℕ, ∀ p : Patch, p.J=j → L₀≤p.L.val →
      (∃ F : Tent history, Notebook (lattice p) Y G Z c (RegulatorIR.FVAAlt2.Rocket.native history) F n) ∧
      SatisfiesQ G Y (lattice p) Z (marked p) n u (1/2) := by
  refine ⟨orders G Y n u j (1/2) (by norm_num) (by norm_num),fun p hp hL=>⟨?_,?_⟩⟩
  · exact notebooks p Y Z c _ n
  · exact budgets p Y Z n u h₁ h₂ (hp.symm ▸ hj) (hp.symm ▸ hL)

end YM.Integration.MSFixedRatioCalibration
