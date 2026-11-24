import YM.Integration.WilsonOriginalFittedLaplacian
import YM.Integration.WilsonSmoothUnitGridSupport

/-! Charge the actual occupied position volume of a compact test, once, in the
four-direction bound on the inherited ordinary word. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalFittedLaplacianSupport
open Finset Set Lattice WilsonSmoothUnitFiniteGrid WilsonPhysicalTestFibre
open scoped BigOperators Classical

theorem original {n:Side}(h R E C D:ℝ)(pos:0<h)(hr:0 ≤ R)(he:0 ≤ E)
    (hc:0 ≤ C)(hd:0 ≤ D)(left lo:Axis → ℝ)(mass:Axis → Site n → ℝ)
    (within:∀a x,mass a x ≤ E)
    (outside:∀a x,(∃j,point (left j) h (x j)∉Icc (lo j) (lo j+R)) → mass a x ≤ 0)
    (reading:ℂ)(priced:‖reading‖≤∑a:Axis,∑y:Slice n a,C*(∑z:Per n,mass a (chart n a (y,z)))*D):
    h^4*‖reading‖≤4*C*D*(R+h)^4*E:=by
  have byaxis:∀a:Axis,h^4*(∑y:Slice n a,C*(∑z:Per n,mass a (chart n a (y,z)))*D)≤C*D*((R+h)^4*E):=by
    intro a
    have grid:(∑y:Slice n a,∑z:Per n,mass a (chart n a (y,z)))=∑x:Site n,mass a x:=by
      simpa only [Fintype.sum_prod_type] using Equiv.sum_comp (chart n a) (mass a)
    rw [← Finset.sum_mul,← Finset.mul_sum,grid]
    have four:=WilsonSmoothUnitGridSupport.four h R E pos hr he left lo (mass a) (within a) (outside a)
    calc h^4*(C*(∑x:Site n,mass a x)*D)=C*D*(h^4*(∑x:Site n,mass a x)):=by ring
         _≤_:=mul_le_mul_of_nonneg_left four (mul_nonneg hc hd)
  calc h^4*‖reading‖≤h^4*(∑a:Axis,∑y:Slice n a,C*(∑z:Per n,mass a (chart n a (y,z)))*D):=
         mul_le_mul_of_nonneg_left priced (by positivity)
       _=∑a:Axis,h^4*(∑y:Slice n a,C*(∑z:Per n,mass a (chart n a (y,z)))*D):=Finset.mul_sum ..
       _≤∑_a:Axis,C*D*((R+h)^4*E):=Finset.sum_le_sum fun a _=>byaxis a
       _=4*C*D*(R+h)^4*E:=by simp [Axis];ring
end YM.Integration.WilsonOriginalFittedLaplacianSupport
