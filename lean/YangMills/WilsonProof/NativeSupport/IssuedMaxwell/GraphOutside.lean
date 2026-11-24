import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphSpectator
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphOutside
open YM YM.FVA2 YM.FVA2.O.Enh Set
theorem original {m:ℕ}(y:Points m):y∈Outside m ↔
    WithLp.toLp 2 (Fin.cons (0:YangMills.Spacetime) y.ofLp)∈YangMills.separated (m+1):=by
  change Function.Injective (Fin.append (fun _:Fin 1=>(0:YangMills.Spacetime)) y.ofLp) ↔
    Function.Injective (Fin.cons (0:YangMills.Spacetime) y.ofLp)
  rw [Fin.append_left_eq_cons]
  constructor
  · intro inject i j eq
    have chosen:=inject (a₁:=Fin.cast (Nat.one_add m).symm i) (a₂:=Fin.cast (Nat.one_add m).symm j) eq
    exact Fin.ext (congrArg (fun p:Fin (1+m)=>p.val) chosen)
  · intro inject
    exact inject.comp (Fin.cast_injective _)
end IssuedMaxwell.GraphOutside
end
