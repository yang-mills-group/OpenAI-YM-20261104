import YM.Integration.WilsonPositionProgramCommonWindow
import YM.FVAAlt2.Periodic.Field

/-! The chronological formal circuit on common copies of the elected variable Wilson blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramVariableCircuit
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2.Period.Field
open WilsonPositionProgramCommonWindow
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))

def remaining (p : Page j) := j p.bindW-p.downW
def date (p : Page j) := m p.bindW+remaining j p
def count (p : Page j) := side D (w p.bindW) (j p.bindW) (remaining j p)

private theorem before (f : Flap j) : remaining j f.prev=remaining j f.next+1 := by
  change j f.volW-f.offset = j f.volW-(f.offset+1)+1
  have := f.ok
  omega

private theorem preceding (f : Flap j) : date m j f.prev=date m j f.next+1 := by
  change m f.volW+remaining j f.prev = m f.volW+remaining j f.next+1
  rw [before j f,Nat.add_assoc]

def circuit : Circuit j (count D j w) where
  l p := ((count D j w (Page.opening j p.bindW)).val : ℝ)/(count D j w p).val
  P x := (count D j w (Page.opening j x)).val
  sizeL f := C.family.S.block (date m j f.next)
  J p := C.family.path.levels.clock.J (date m j p)
  seats f := by
    apply Subtype.ext
    change (side D (w f.volW) (j f.volW) (remaining j f.prev)).val =
      (side D (w f.volW) (j f.volW) (remaining j f.next)).val * (C.family.S.block (m f.volW+remaining j f.next)).val
    rw [before j f]
    exact edge C D (m f.volW) (w f.volW) (blocks f.volW) _ _
  odd f := C.family.S.block_odd _
  holds f := C.family.S.block_large _
  stands p := D.finalSide.large.trans (Nat.le_mul_of_pos_right _ (D.den_pos _))
  dual p := even_iff_two_dvd.mpr (dvd_mul_of_dvd_left D.finalSide.even _)
  week p := C.family.path.levels.clock.adm _
  shakes f := by rw [preceding m j f]; exact C.family.path.levels.fits.mono (Nat.le_succ _)
  slow f := by rw [preceding m j f]; exact C.family.path.levels.fits.stepSlow _
  l_p p := div_pos (by exact_mod_cast (count D j w _).property) (by exact_mod_cast (count D j w p).property)
  comet p := div_mul_cancel₀ _ (by exact_mod_cast (count D j w p).property.ne')

private theorem equal_patch {P Q : RG.Patch} (hL : P.L=Q.L) (hJ : P.J=Q.J) : P=Q := by
  cases P; cases Q; cases hL; cases hJ; rfl

/-- The historical patch and kernel agree on every original physical period, before a copy is evaluated. -/
def history : SeriesT (circuit C D m j w blocks) C.family.path.levels.clock.kernel C.family.path where
  vol := date m j
  links := preceding m j
  pact f per := by
    refine equal_patch (P:=(C.family.path.levels.clock.op (date m j f.next) per).patch)
      (Q:=(circuit C D m j w blocks).pactP f) rfl ?_
    exact congrArg C.family.path.levels.clock.J (preceding m j f).symm
  creed _ _ := rfl

theorem top (x : X) : count D j w (Page.opening j x)=(D.step (elapsed (w x) (j x))).p.side := by
  simpa only [count,remaining,Page.opening,Nat.sub_zero] using fine D (w x) (j x)

theorem reported (x : X) : (history C D m j w blocks).vol (Page.finallyW j x)=m x := by
  change m x+(j x-j x)=m x
  omega

end YM.Integration.WilsonPositionProgramVariableCircuit
end
