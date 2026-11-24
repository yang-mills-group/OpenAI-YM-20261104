import YM.Integration.WilsonOlderFreshSoftSocketInitial
import Mathlib.Algebra.QuadraticAlgebra.Defs

/-! Finite products of the genuinely complex paid original doses across an ordinary face, tested by any real-linear return of the complete phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketPhases
open Finset
open scoped Classical BigOperators QuadraticAlgebra
variable {A:Type}[CommRing A][Algebra ℝ A]
local notation "Z_" => QuadraticAlgebra A (-1) 0
private def tint (z:ℂ)(x:A):Z_:=⟨z.re • x,z.im • x⟩
private theorem mixed (z w:ℂ)(x y:A):
    tint (z*w) (x*y)=tint z x*tint w y:=by
  apply QuadraticAlgebra.ext
  · simp only [tint,QuadraticAlgebra.re_mul,Complex.mul_re,Algebra.smul_def,map_sub,map_mul]
    ring
  · simp only [tint,QuadraticAlgebra.im_mul,Complex.mul_im,Algebra.smul_def,map_add,map_mul]
    ring

private theorem placed {I:Type}(s:Finset I)(a:I→ℂ)(b:I→A):
    tint (∏i∈s,a i) (∏i∈s,b i)=∏i∈s,tint (a i) (b i):=by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tint,QuadraticAlgebra.ext_iff]
  | insert v s hv ih => rw [prod_insert hv,prod_insert hv,prod_insert hv,mixed,ih]

private def view (L:ℂ→L[ℝ]ℝ):Z_ →+ A where
  toFun z:=L 1 • z.re+L Complex.I • z.im
  map_zero':=by simp
  map_add' x y:=by simp [smul_add];abel
private theorem replay (L:ℂ→L[ℝ]ℝ)(z:ℂ)(a:A):view L (tint z a)=L z • a:=by
  have dec:(z.re:ℂ)+(z.im:ℂ)*Complex.I=z:=Complex.re_add_im z
  have coordinates:z.re • (1:ℂ)+z.im • Complex.I=z:=by simpa only [Complex.real_smul,mul_one] using dec
  have eq:=congrArg L coordinates
  rw [map_add,L.map_smul,L.map_smul] at eq
  change L 1 • z.re • a+L Complex.I • z.im • a=L z • a
  simp only [←eq,add_smul,smul_smul,smul_eq_mul,mul_comm]

theorem original {I:Type}[Fintype I]{J:I→Type}[∀i,Fintype (J i)](source:I→A)
    (socket:(i:I)→J i→A)(charge:(i:I)→J i→ℂ)
    (receipt:∀i(L:ℂ→L[ℝ]ℝ), L 1 • source i=∑q,L (charge i q) • socket i q)
    (L:ℂ→L[ℝ]ℝ):L 1 • (∏i,source i)=
      ∑q:(i:I)→J i,L (∏i,charge i (q i)) • (∏i,socket i (q i)):=by
  classical
  have axis (i:I):tint 1 (source i)=∑q,tint (charge i q) (socket i q):=by
    apply QuadraticAlgebra.ext
    · change _=QuadraticAlgebra.reₗ (-1:A) 0 (∑q,tint (charge i q) (socket i q))
      rw [map_sum]
      exact receipt i Complex.reCLM
    · change _=QuadraticAlgebra.imₗ (-1:A) 0 (∑q,tint (charge i q) (socket i q))
      rw [map_sum]
      exact receipt i Complex.imCLM
  have all:tint 1 (∏i,source i)=∑q:(i:I)→J i,tint (∏i,charge i (q i)) (∏i,socket i (q i)):=by
    calc
      _=∏i,tint 1 (source i):=by simpa using placed univ (fun _:I=>(1:ℂ)) source
      _=∏i,∑q,tint (charge i q) (socket i q):=Finset.prod_congr rfl fun i _=>axis i
      _=_:=by rw [Fintype.prod_sum];apply Finset.sum_congr rfl;intro q _;exact (placed univ ..).symm
  have h:=congrArg (view L) all
  simpa only [map_sum,replay] using h

end YM.Integration.WilsonOlderFreshSoftSocketPhases
end
