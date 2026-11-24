import YM.Integration.WilsonThermometerUnitFilingWeakSpoke
import YM.Integration.WilsonThermometerUnitFilingWeakTrunk

/-! Sum the free end of a true contracted covariance and every leg of its older vacuum vertex. The residue in the actual subdivided fine block remains in the price. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakJoin
open Function Filter Finset Lattice Laurent Bloch Precision RG Next.Free Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonThermometerUnitFilingWeakTrunk
open scoped Classical BigOperators
variable {I J α E:Type*} [NormedAddCommGroup E]

private theorem choice (n:Side)(y:Site n):
    ∃d:Cover,wrap n d=y ∧ ∀z:Cover,wrap n z=y → size d ≤ size z:=by
  let h:∃l:ℕ,∃d:Cover,wrap n d=y ∧ size d=l:=⟨_,lift y,wrap_lift _,rfl⟩
  obtain ⟨d,eq,fare⟩:=Nat.find_spec h
  exact ⟨d,eq,fun z hz=>fare ▸ Nat.find_min' h ⟨z,hz,rfl⟩⟩

def nearest (n:Side)(y:Site n):Cover:=(choice n y).choose

theorem joins (n:Side)(y:Site n):wrap n (nearest n y)=y:=(choice n y).choose_spec.1

def stretch (L:Side)(d:Cover):Cover:=fun a=>(L.val:ℤ)*d a

private theorem length (L:Side)(d:Cover):size (stretch L d)=L.val*size d:=by
  simp [Laurent.size,stretch,Int.natAbs_mul,Finset.mul_sum]

def vertex {k:ℕ}(n:Side)(L:Side)(x offset o:Cover)(t:ℝ)(g:α)
    (V:Ten E (Cloth α) (k+1))(y:Site n):ℝ:=
  ∑'z:Fin k→Cloth α,coat (t/(k+1)) o z*
    ‖V (Fin.cons (stretch L x+offset+stretch L (nearest n (y-wrap n x)),g) z)‖

theorem priced (A:Bloch.Row I J)(n:Side)(L:Side)(x offset o:Cover)(i:I)(j:J)(g:α)
    {k:ℕ}(V:Ten E (Cloth α) (k+1)){s c t B:ℝ}(paid:A.strip s c)(bp:0 ≤ B)(tp:0 ≤ t)
    (scale : t*(L.val:ℝ) ≤ s)
    (trunk:∀z:Cover,SumBudget (fun u:Fin k→Cloth α=>coat (t/(k+1)) o u*‖V (Fin.cons (z,g) u)‖)
      (Real.exp (t*size (z-o))*B)):
    ∑y:Site n,|A.acts n (wrap n x,i) (y,j)| *vertex n L x offset o t g V y ≤
      c*(Real.exp (t*size (stretch L x+offset-o))*B):=by
  have nonneg (y:Site n):0≤ vertex n L x offset o t g V y:=
    tsum_nonneg (trunk _).1
  apply WilsonThermometerUnitFilingWeakSpoke.absolute A paid
    (mul_nonneg (Real.exp_pos _).le bp) n (wrap n x) i j _ nonneg
  intro d
  let y:=wrap n x+wrap n d
  let z:=nearest n (y-wrap n x)
  have small:size z≤ size d:=(choice n (y-wrap n x)).choose_spec.2 d (by simp [y])
  have far:(size (stretch L x+offset+stretch L z-o):ℝ) ≤
      (size (stretch L x+offset-o):ℝ)+(L.val:ℝ)*(size d:ℝ):=by
    rw [show stretch L x+offset+stretch L z-o=(stretch L x+offset-o)+stretch L z by abel]
    have step:=(size_add (stretch L x+offset-o) (stretch L z)).trans
      (Nat.add_le_add_left ((length L z).le.trans (Nat.mul_le_mul_left _ small)) _)
    exact_mod_cast step
  calc _ ≤ Real.exp (t*size (stretch L x+offset+stretch L z-o))*B:=(trunk _).2.2
       _ ≤ Real.exp (s*size d+t*size (stretch L x+offset-o))*B:=by
         apply mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) bp
         calc _≤ t*((size (stretch L x+offset-o):ℝ)+(L.val:ℝ)*(size d:ℝ)):=mul_le_mul_of_nonneg_left far tp
              _≤_:=by nlinarith only [mul_nonneg (sub_nonneg.mpr scale) (Nat.cast_nonneg (α:=ℝ) (size d))]
       _ = _:=by rw [Real.exp_add,mul_assoc]

end YM.Integration.WilsonThermometerUnitFilingWeakJoin
