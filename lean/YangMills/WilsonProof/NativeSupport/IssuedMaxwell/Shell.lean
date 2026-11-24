import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.WilsonBridge
import YM.Extra.FREE_DETECTOR_ALGEBRA.Dialog
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Shell
open YangMills YM Maxwell
open scoped Matrix.Norms.Frobenius InnerProductSpace Classical
variable (g:YangMills.GaugeGroup)
theorem onShell {j:ℕ}(A:YangMills.Maxwell.TwoJet g.core.lieDim j):
    A∈YM.Maxwell.onShell g.core.Color j ↔ YangMills.Maxwell.OnShell A:=by
  constructor
  · rintro ⟨closed,divergence⟩
    exact ⟨closed.coeffSym,closed.antisymmetric,closed.closed,divergence⟩
  · rintro ⟨symmetry,antisymmetric,cyclic,divergence⟩
    exact ⟨⟨symmetry,antisymmetric,cyclic⟩,divergence⟩

theorem colors:LinearMap.range g.core.colorMat=g.lieAlgebra:=by
  ext x
  constructor
  · rintro ⟨c,rfl⟩
    exact (g.generates _).2 (g.core.colorMat_mem c)
  · intro hx
    have native:x∈g.core.lie:=(g.generates x).1 hx
    refine ⟨g.core.colorIso.symm ⟨x,native⟩,?_⟩
    exact congrArg Subtype.val (g.core.colorIso.apply_symm_apply ⟨x,native⟩)

theorem actionValue (u:g.image)(j)(A:YM.Maxwell.Shell g.core j)
    (a b:YangMills.Axis)(v:Fin j→YangMills.Spacetime):
    (YM.Extra.FD.actionG (G:=g.core) u j A).val a b v=g.core.adjoint u (A.val a b v):=rfl

theorem actionMatrix (u:g.image)(j)(A:YM.Maxwell.Shell g.core j)
    (a b:YangMills.Axis)(v:Fin j→YangMills.Spacetime):
    g.core.colorMat ((YM.Extra.FD.actionG (G:=g.core) u j A).val a b v)=
      g.core.mat u*g.core.colorMat (A.val a b v)*star (g.core.mat u):=by
  rw [actionValue]
  exact g.core.mat_adjoint u (A.val a b v)

def coordinates:YangMills.Maxwell.Coordinates g where
  m:=g.core.lieDim
  matrix:=g.core.colorMat
  colors:=colors g
  traceForm:=g.core.trace_color
  shell:=YM.Maxwell.onShell g.core.Color
  shell_iff:=fun _ A=>onShell g A
  rank:=YM.Maxwell.legDim g.core
  basis:=YM.Maxwell.frame g.core
  rotate:=fun u j=>YM.Extra.FD.actionG (G:=g.core) u j
  adjoint:=actionMatrix g

theorem original: (coordinates g).matrix=g.core.colorMat ∧
    (∀j,(coordinates g).shell j=YM.Maxwell.onShell g.core.Color j) ∧
    ∀j,(coordinates g).basis j=YM.Maxwell.frame g.core j:=
  ⟨rfl,fun _=>rfl,fun _=>rfl⟩
end IssuedMaxwell.Shell
end
