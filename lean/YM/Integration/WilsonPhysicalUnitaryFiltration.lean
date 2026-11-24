import YM.Integration.WilsonPhysicalReflectedBranchWitness
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! An isometry with a strictly filtered deviation fixes the entire original reflected quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalUnitaryFiltration
open Finset Function Filter Lattice Wilson RG Source Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical WilsonPositionProgramPublicContrast
open WilsonPhysicalPositiveHome (appointed)
open WilsonPositionProgramPublicWickGram (reading nodes)
open scoped Classical BigOperators Matrix Topology
variable {I:Type}[Fintype I]

theorem parallelogram (q:I→I→ℂ)(x y:I→ℂ):
    assay (x+y) (x+y) q + assay (x-y) (x-y) q = (2:ℂ)*(assay x x q+assay y y q):=by
  unfold assay
  simp only [Pi.add_apply,Pi.sub_apply,star_add,star_sub]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib,Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _=>by ring

theorem no_drift (q:I→I→ℂ)(T:Module.End ℂ (I→ℂ))
    (orth:∀x,(assay (T x) (T x) q).re=(assay x x q).re)
    (pd:∀x:I→ℂ,x≠0 → 0<(assay x x q).re)
    (nil:IsNilpotent (T-LinearMap.id)):T=LinearMap.id:=by
  let A:Module.End ℂ (I→ℂ):=T-LinearMap.id
  have near (x:I→ℂ):T x=x+A x:=by change T x=x+(T x-x);abel
  have cancel (x:I→ℂ)(one:A (A x)=0):A x=0:=by
    have fixed:T (A x)=A x:=by rw [near (A x),one,add_zero]
    have back:T (x-A x)=x:=by rw [map_sub,fixed,near x,add_sub_cancel_right]
    by_contra bad
    have positive:=pd (A x) bad
    have plus:=orth x
    rw [near x] at plus
    have minus:=(orth (x-A x)).symm
    rw [back] at minus
    have gap:=congrArg Complex.re (parallelogram q x (A x))
    norm_num [Complex.add_re,Complex.mul_re] at gap
    linarith
  have one (k:ℕ)(x:I→ℂ)(last:(A^k) x=0):A x=0:=by
    induction k generalizing x with
    | zero =>
      have h:x=0:=by simpa only [pow_zero,Module.End.one_apply] using last
      rw [h,map_zero]
    | succ k ih => exact cancel x (ih (A x) (by simpa only [pow_succ,Module.End.mul_apply] using last))
  obtain ⟨k,stop⟩:=nil
  apply LinearMap.ext
  intro x
  have null:A x=0:=one k x (by rw [show A^k=0 from stop];rfl)
  exact sub_eq_zero.mp (show T x-x=0 from null)

theorem filtered [DecidableEq I] (rank:I→ℕ)(A:Matrix I I ℂ)
    (down:∀i j,rank i≥rank j → A i j=0):IsNilpotent A:=by
  have path (k:ℕ)(i j:I)(miss:rank j<rank i+k):(A^k) i j=0:=by
    induction k generalizing i j with
    | zero =>
      have ne:i≠j:=fun eq=>by subst j;omega
      simp [ne]
    | succ k ih =>
      rw [pow_succ,Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro w _
      by_cases close:rank w<rank i+k
      · simp only [ih i w close,zero_mul]
      · simp only [down w j (by omega),mul_zero]
  let cap:=Finset.univ.sup rank
  refine ⟨cap+1,?_⟩
  ext i j
  have below:rank j≤cap:=Finset.le_sup (f:=rank) (Finset.mem_univ j)
  exact path _ i j (by omega)

theorem original {G:Gauge}(B:Local.Physical.Deck G)(h:ℕ)(a:Axis)
    (rank:Glyph B h→ℕ)(M:Matrix (Glyph B h) (Glyph B h) ℂ)
    (down:∀i j,rank i≥rank j → (M-1) i j=0)
    (orth:∀x,(assay (M*ᵥx) (M*ᵥx) (reading a (nodes a) (id:Glyph B h→Glyph B h))).re=
      (assay x x (reading a (nodes a) (id:Glyph B h→Glyph B h))).re):M=1:=by
  let q:=reading a (nodes a) (id:Glyph B h→Glyph B h)
  let φ:=Matrix.toLinAlgEquiv' (R:=ℂ) (n:=Glyph B h)
  have conversion:φ (M-1)=φ M-LinearMap.id:=by rw [map_sub,map_one];rfl
  have nil:IsNilpotent (φ M-LinearMap.id):=by
    obtain ⟨k,stop⟩:=filtered rank (M-1) down
    refine ⟨k,?_⟩
    rw [←conversion,←map_pow,←map_zero φ]
    apply congrArg (fun A:Matrix (Glyph B h) (Glyph B h) ℂ=>φ A)
    exact stop
  have collapse:=no_drift q (φ M) orth (fun x non=>?_ ) nil
  · apply φ.injective
    rw [map_one]
    exact collapse
  · let floor:=appointed B h a
    have limit:=floor.paid q (by simpa only [q,sub_self,norm_zero] using floor.aperture.le) x
    exact (mul_pos floor.positive (pow_pos (norm_pos_iff.mpr non) 2)).trans_le limit

end YM.Integration.WilsonPhysicalUnitaryFiltration
