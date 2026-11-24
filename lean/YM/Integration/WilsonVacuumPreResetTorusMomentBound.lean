import YM.WilsonCoeffUV.Ward.Moments
import YM.WilsonCoeffUV.Thermo.Transfer

/-! A summable majorant on the original relative coordinate lattice,
including the polynomial distance used by affine curvature probes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusMomentBound
open Filter Function Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank
open Matrix RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open scoped Classical BigOperators Topology
variable {α:Type*}{k:ℕ}{n:Side}

def housing (x:Cloth α)(y:dock Cover α k)(n:Side):Prop:=unfoldAt x.1 (slideC n y)=y

def width (u:ℝ)(k:ℕ):ℝ:=u/(max 1 k:ℕ)

theorem positive {u:ℝ}(hu:0<u)(k:ℕ):0<width u k:=by
  unfold width
  exact div_pos hu (Nat.cast_pos.mpr (by omega))

private theorem decay {u:ℝ}(hu:0<u)(x:Cloth α)(y:dock Cover α k)
    {d:ℕ}(bounded:∀i,terrain.gap x.1 (y i).1≤d):
    Real.exp (-u*d)≤sail (width u k) terrain x.1 y:=by
  by_cases h:k=0
  · subst k
    simp only [sail,Finset.univ_eq_empty,Finset.prod_empty]
    exact Real.exp_le_one_iff.mpr (by nlinarith [show (0:ℝ)≤d by positivity])
  have one:1≤k:=by omega
  rw [width,max_eq_right one]
  simpa only [sub_zero,neg_zero,zero_mul,Real.exp_zero,one_mul] using
    sail_cut (d:=terrain) (Nat.zero_le d) le_rfl hu one x.1 y bounded

theorem at_root {V:Type*}[NormedAddCommGroup V]{σ A:ℝ}{F:Ten V (Co n α) (k+1)}
    (income:Amber (tor n) σ A F)(warm:0<σ)(d:ℕ)
    (x:Cloth α)(y:dock Cover α k)(kept:housing x y n):
    let row:=Fin.cons (foldUnder n x) (slideC n y)
    (1+soar (tor n) row:ℝ)^d*‖F row‖≤
      (A*ceilPoly d (σ-σ/2))*sail (width (σ/2) k) terrain x.1 y:=by
  intro row
  have half:0<σ/2:=half_pos warm
  have rays (i:Fin k):terrain.gap x.1 (y i).1≤soar (tor n) row:=by
    have same:=near_change x.1 (slideC n y) i
    change unfoldAt x.1 (slideC n y)=y at kept
    rw [kept] at same
    rw [same]
    exact leg_le (tor n) (Prod.fst ∘ row) 0 (Fin.succ i)
  have fee:=mul_le_mul_of_nonneg_left (income.2 row) (show 0≤(1+soar (tor n) row:ℝ)^d by positivity)
  calc
    _≤A*((1+soar (tor n) row:ℝ)^d*Real.exp (-σ*soar (tor n) row)):=by linarith only [fee]
    _≤A*(ceilPoly d (σ-σ/2)*Real.exp (-(σ/2)*soar (tor n) row)):=
      mul_le_mul_of_nonneg_left (poly_used d (show σ/2<σ by linarith) _) income.1
    _≤_:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_left (decay half x y rays) (mul_nonneg income.1 (ceilPoly_pos ..).le)

end YM.Integration.WilsonVacuumPreResetTorusMomentBound
