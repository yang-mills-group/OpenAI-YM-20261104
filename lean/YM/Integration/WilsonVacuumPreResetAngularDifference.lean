import YM.Integration.WilsonVacuumPreResetGraftedField
import YM.Integration.WilsonVacuumPreResetCanonicalPrefix
import YM.Integration.WilsonVacuumPreResetIndependentHistory

/-! Express the change of the signed old polynomial in the actual finite and
periodized cover angular tensors at the same date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetAngularDifference
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior PhysicalNext.Repeat.Legato
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Series FormalBulk08.Shore FormalBulk08.Lotus
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open Next.Rank
open scoped Classical BigOperators Topology
variable {G:Gauge}

private theorem tensor {U:Type}[Fintype U](r:ℕ)(T:Ten ℝ U r):
    let P:=MvPolynomial.map Complex.ofRealHom (paint r T)
    Rise.coin P≤∑v,|T v| ∧ P.totalDegree≤r:=by
  intro P
  have unfoldP:P=∑v:Fin r→U,MvPolynomial.C (Complex.ofRealHom (T v))*∏ a,MvPolynomial.X (v a):=by
    change MvPolynomial.map _ (∑v:Fin r→U,T v • ∏ a,MvPolynomial.X (v a))=_
    simp [Algebra.smul_def,map_sum,map_prod,MvPolynomial.algebraMap_eq]
  rw [unfoldP]
  refine ⟨(Rise.collect _ zero_le_one _ _).trans (Finset.sum_le_sum fun v _=>?_),?_⟩
  · have h:Rise.coin (∏a:Fin r,MvPolynomial.X (v a):MvPolynomial U ℂ)≤1:=by
      simpa [Rise.coin] using Rise.purchased (0:U→ℕ) (r:=1) zero_le_one univ
        (fun a:Fin r=>(MvPolynomial.X (v a):MvPolynomial U ℂ))
    calc
      _≤Rise.coin (MvPolynomial.C (Complex.ofRealHom (T v)):MvPolynomial U ℂ)*Rise.coin (∏a:Fin r,MvPolynomial.X (v a):MvPolynomial U ℂ):=Rise.funds _ zero_le_one _ _
      _≤Rise.coin (MvPolynomial.C (Complex.ofRealHom (T v)):MvPolynomial U ℂ)*1:=
        mul_le_mul_of_nonneg_left h (Rise.sign _ _ zero_le_one)
      _=|T v|:=by simp [Rise.coin,Real.norm_eq_abs]
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro v _
    apply (MvPolynomial.totalDegree_mul ..).trans
    rw [MvPolynomial.totalDegree_C,zero_add]
    apply (MvPolynomial.totalDegree_finsetProd ..).trans
    simp

variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
local notation "O" => R.metals.O
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)

/-- True finite tensors and the periodized covered tensors. All ranks are
jointly retained, including angular rank zero. -/
theorem original (simple:G.Simple)(N j:ℕ)(date:j≤N)
    (filed:WilsonVacuumPreResetIndependentHistory.Filed R u N j)(n:Side)(e:ℕ):
    let A:=(story V O N j).1 n
    let T:=emera (actionW V O N j) n
    let D:=WilsonVacuumPreResetFiniteIntegral.read R N j n-
      Mesa.stone (Dove.model V wood b O u N j) n
    let P:=MvPolynomial.map Complex.ofRealHom (PowerSeries.coeff e D)
    Rise.coin P≤∑r∈Finset.range (e+3),∑x,|T e r x-A e r x| ∧ P.totalDegree≤e+2:=by
  intro A T D P
  have registered:=WilsonVacuumPreResetCanonicalPrefix.retained R simple N j date
    (Dove.model V wood b O u N j) e (fun k _ r _=>filed k r) n e le_rfl
  have upper:=((old V O simple R.alloy.B.ratio N j date).basis n).lamp
  have covered:=(emera_far V simple R.alloy.B.ratio date n).1
  have AA:still (A e) (e+3):=fun r hr=>upper e r (by omega)
  have TT:still (T e) (e+3):=fun r hr=>covered e r (by omega)
  have row:P=∑r∈Finset.range (e+3),MvPolynomial.map Complex.ofRealHom (paint r (T e r-A e r)):=by
    change MvPolynomial.map _ (PowerSeries.coeff e (-flash A-Mesa.stone _ n))=_
    rw [map_sub,←registered]
    change MvPolynomial.map _ (PowerSeries.coeff e (-flash A)-PowerSeries.coeff e (-flash T))=_
    simp only [map_neg,flash,PowerSeries.coeff_mk,visible AA,visible TT,map_sub,map_sum,
      Finset.sum_sub_distrib]
    abel
  rw [row]
  refine ⟨(Rise.collect _ zero_le_one _ _).trans (Finset.sum_le_sum fun r _=>(tensor r (T e r-A e r)).1),?_⟩
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r hr
  exact (tensor r _).2.trans (by have:=Finset.mem_range.mp hr;omega)

end YM.Integration.WilsonVacuumPreResetAngularDifference
end
