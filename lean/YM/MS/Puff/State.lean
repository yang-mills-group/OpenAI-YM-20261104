import YM.MS.Puff.Euler
import YM.MS.Puff.Live

set_option autoImplicit false
noncomputable section
namespace YM.MS.Puff.Mom
open Set Filter Function Finset Metric Real
open Book Convolve
open SplitP Actors
open scoped Topology
variable {W : Type} [LinearOrder W]
def Toy : Actors ℂ:={
    guard:=⊤
    core:= Algebra.lmul ℂ ℂ
    unit:=1
    holds:=Submodule.mem_top
    close:= fun _ _ _ _=> Submodule.mem_top
    identityK x:=one_mul x
    identityR x:=mul_one x
    turns u _ v _:= mul_comm u v
    star_a x y z:=mul_assoc x y z }
abbrev Trunk : Actors ( T ℂ ):= Toy.stack useN
def bouquet (F:Finset W→ T ℂ ): Finset W→T ℂ:= Cheer Trunk ( marked W ) F
end YM.MS.Puff.Mom
