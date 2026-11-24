import YangMills.WilsonProof.NativeSupport.FundedScalarDisk
import YM.FullVolume.Nectar.Emits

/-! A funded marked sector through each native successor. Its frame slots
come from the selected run, and the labelled incoming activities are exactly
constant along the whole real scalar curve. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open RG Wilson Lattice PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Campaign PhysicalNext.Repeat.Muse
open PhysicalNext.Repeat.Pass PhysicalNext.Repeat.Jams PhysicalNext.Repeat.Muse.Veil
open Extra.Iteration FullVolume.Ray FullVolume.Urns Progress.DirectedRecipe
open scoped Classical
variable {G : Gauge} {R : Run G} (T : Campaign R) {N per : ℕ}

theorem physical_scalar_sector (i : Fin N) :
    let O := halls T per N
    let p := T.center N per
    let j := i.val+1
    let P := R.alloy.B.a.clock.hatBeta j
    ∃ F : sun → Board (A:=R.alloy) N i per (O.plan j i.isLt),
      (∀ s : sun,
        (F s).val.val.val.activities = (R.T.history N per j).activities ∧
        (F s).val.val.val.beta = fromLambda P (p.pitch i.succ+s.val)) ∧
      (∃ Y, SectorOn (A:=R.alloy) (fun s => (F s).val.val) Y) ∧
      fromLambda P (p.pitch i.succ) = (R.T.history N per j).beta := by
  dsimp only
  let O := halls T per N
  let p := T.center N per
  let j := i.val+1
  let H := T.L.prim N i per i.isLt
  let S := O.plan j i.isLt
  let P := R.alloy.B.a.clock.hatBeta j
  have idA : observe S (p.chair T.gains O i.succ) = (R.T.history N per j).activities :=
    p.home_observe T.gains O j i.isLt
  have hs := R.tuning.receipts.samples T.gains.SimpleR N j per i.isLt
  have hp := (R.T.choice.represents N per j i.isLt).vac
  have has : HasSlots (R.alloy.B.a.budget j) (observe S (p.chair T.gains O i.succ)) := by
    rw [idA]
    rw [hp] at hs
    exact hs
  let x : ℝ × Nilot S := (p.pitch i.succ,⟨p.chair T.gains O i.succ,has⟩)
  let w : ℝ × Nilot S := (1,0)
  let point (s : sun) := x+s.val • w
  have fixed (s : sun) : (point s).2 = x.2 := by simp [point,w]
  have scalar (s : sun) : (point s).1 = p.pitch i.succ+s.val := by simp [point,x,w]
  have hid : observe S x.2.val = (R.T.history N per j).activities := idA
  have climate := T.gains.largeG.scale j
  have center : emcee P x.1 :=
    Pass.samples climate (p.mildS T.gains j i.isLt) (sub_self x.1 ▸ (by norm_num))
  have band (s : sun) : fromLambda P (point s).1 ∈ RG.Shoot.band R.alloy.B.a j := by
    exact Pass.band_full R.alloy.B.a climate center (u':=w.1) (by norm_num [w]) s
  have small (s : sun) : ‖(point s).2‖ ≤ 1 := by
    rw [fixed]
    exact (p.sparkN T.gains O i.succ).trans (by norm_num)
  let f (s : sun) := glades H (point s)
  have reads (s : sun) : ReadsF (f s) (point s) := gleans H _ (band s) (small s)
  let F (s : sun) : Board (A:=R.alloy) N i per S := ⟨f s,point s,reads s⟩
  refine ⟨F,?_,trailP climate f x w center (by norm_num [w]) reads, p.spoken T.gains j i.isLt⟩
  intro s
  have h₁ := (reads s).bills
  rw [fixed,hid] at h₁
  exact ⟨h₁, (reads s).takes.trans (congrArg (fromLambda P) (scalar s))⟩

end YM.Integration.InletSusceptibility
