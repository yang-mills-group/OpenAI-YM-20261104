import YM.Qlocal.Quipu.Stew
import YM.AllOrder.Floe.Stars
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu
open AllOrder AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method GaussianScore Module Kinetic
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {α β : Type} [Fintype α] [Fintype β] {k N M:ℕ} {a C D b:ℝ}
-- projection by local injection, any Fin coords. including additive reassemblings.L echoes
variable (f:α→β)
def skirt [DecidableEq β] (f:α→β) : Stalk α β:= fun i=> Work.F08.unitRow β (f i)
variable [DecidableEq β]
omit [Fintype α] [Fintype β] in
lemma skirt_rents : Belt (skirt f) a 1:= fun i j=> (paid_identity (α:=β) (a:=a) RealSlice.three).1 (f i) j
lemma knead (x:rule β n): know (skirt f) n x= here f x:= by
 funext i; change ∑j:Leaf n β,direct (skirt f) n i j * _=_
 have h j : direct (skirt f) n i j= if j= (i.1,f i.2) then 1 else 0:= by
    rw [direct,Matrix.of_apply,tsum_eq_single (0:Cover)]; swap; · intro j hh; simp [skirt,Work.F08.unitRow,hh]
    rcases j with ⟨t,l⟩; by_cases h:t=i.1 <;> simp [skirt,Work.F08.unitRow,h, eq_comm (a:=f i.2)]
 simp_rw [h,ite_mul]; simp; rfl
end YM.Qlocal.Quipu
