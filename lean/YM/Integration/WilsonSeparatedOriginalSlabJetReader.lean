import YM.Integration.WilsonSeparatedOriginalSlabPlaneTest
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.Isomorphisms

/-! The native marked stencil on a smooth wave is a single bounded complex-linear reader of its genuine Fréchet jet, common to every spatial location. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabJetReader
open Function Set RG05Readout RG05Readout.Native RG05Readout.Pulse
open scoped BigOperators Classical Topology ContDiff
local notation "Y"=>Cloud (Fin 3)
local notation "W"=>Wave (Fin 3)
local notation "T" n=>Tensor.T Y ℂ n

def jet (m:ℕ)(x:Y):W→ₗ[ℂ]T m where
  toFun f:=iteratedFDeriv ℝ m f.val x
  map_add' f g:=iteratedFDeriv_add_apply (lit f m).contDiffAt (lit g m).contDiffAt
  map_smul' c f:=iteratedFDeriv_const_smul_apply (a:=c) (lit f m).contDiffAt

def probe (s:Fin 3→ℕ)(k:(i:Fin 3)→Letter (s i))(x:Y):W→ₗ[ℂ]ℂ where
  toFun f:=(perform s k f).val x
  map_add' f g:=by rw [map_add];rfl
  map_smul' c f:=by rw [map_smul];rfl

private theorem dimension (m:ℕ):FiniteDimensional ℂ (T m):=by
  let F:(T m)→ₗ[ℝ]MultilinearMap ℝ (fun _:Fin m=>Y) ℂ:=ContinuousMultilinearMap.toMultilinearMapLinear
  letI : FiniteDimensional ℝ (T m):=FiniteDimensional.of_injective F ContinuousMultilinearMap.toMultilinearMap_injective
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ _

theorem original (s:Fin 3→ℕ)(k:(i:Fin 3)→Letter (s i)):
    let m:=pegs s k Finset.univ.toList
    ∃ price:(T m)→L[ℂ]ℂ,∀(f:W)(x:Y),(perform s k f).val x=price (iteratedFDeriv ℝ m f.val x):=by
  intro m
  let A:=jet m (0:Y)
  let B:=probe s k (0:Y)
  have gate:LinearMap.ker A≤LinearMap.ker B:=by
    intro f hf
    have same:pie f 0 m (0:Y):=by
      change A f=A 0
      rw [map_zero];exact hf
    change (perform s k f).val 0=0
    rw [performance s k same,map_zero];rfl
  let H:LinearMap.range A→ₗ[ℂ]ℂ:=((LinearMap.ker A).liftQ B gate).comp A.quotKerEquivRange.symm.toLinearMap
  obtain ⟨back,undo⟩:=(LinearMap.range A).subtype.exists_leftInverse_of_injective (LinearMap.ker_eq_bot_of_injective Subtype.val_injective)
  let L:=H.comp back
  letI:FiniteDimensional ℂ (T m):=dimension m
  let paid:(T m)→L[ℂ]ℂ:={toLinearMap:=L,cont:=L.continuous_of_finiteDimensional}
  refine ⟨paid,?_⟩
  have atZero (f:W):B f=L (A f):=by
    have hb:back (A f)=A.rangeRestrict f:=DFunLike.congr_fun undo (A.rangeRestrict f)
    change B f=H (back (A f));rw [hb]
    change B f=(LinearMap.ker A).liftQ B gate (A.quotKerEquivRange.symm ⟨A f,_⟩)
    rw [A.quotKerEquivRange_symm_apply_image];rfl
  intro f x
  have here:=atZero (fork 1 x f)
  change (perform s k (fork 1 x f)).val 0=L (iteratedFDeriv ℝ m (fork 1 x f).val 0) at here
  have move: (fork 1 x f).val=(fun y=>f.val (x+y)):=by funext y;change f.val (x+1 • y)=_;rw [one_smul]
  rw [move,iteratedFDeriv_comp_add_left,add_zero] at here
  rw [show perform s k (fork 1 x f)=(1:ℂ)^m • fork 1 x (perform s k f) from by simpa [m] using machine_roll s k Finset.univ.toList (1:ℝ) x f,one_pow,one_smul] at here
  change (perform s k f).val (x+1 • (0:Y))=L (iteratedFDeriv ℝ m f.val x) at here
  change (perform s k f).val x=L (iteratedFDeriv ℝ m f.val x)
  simpa only [smul_zero,add_zero] using here

end YM.Integration.WilsonSeparatedOriginalSlabJetReader
