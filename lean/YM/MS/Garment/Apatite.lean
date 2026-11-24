import YM.MS.Arts.Pilot
import YM.MS.Color.Group

set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux Landau Arts Pilot
open Momentum Metric Color
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {b: Bool}
variable {D P: Type} [Fintype D] [DecidableEq D] [AddCommGroup P]
def dye (g:G.El): Pilot ℂ P (Landau.parity (C:=G.ColorIndex) (A:=D)) where
   volp:= AddEquiv.refl _
   fieldC a b:= if a.1=b.1 then wc g a.2 b.2 else 0
   pair_zero a b h:= by split_ifs at h with ht; exact congr_arg Landau.p ht; contradiction
lemma brush (g:G.El) : (dye (D:=D) (P:=P) g).beam=Color.repeatC g:= by
   apply LinearMap.ext; intro X; funext l; induction l generalizing X with
   | nil=> simp
   | cons i l ih=> rw [Pilot.met,repeat_cons]; simp only [ih]; rw [Fintype.sum_prod_type]; unfold dye; simp [ite_mul]
end YM.MS.Garment
