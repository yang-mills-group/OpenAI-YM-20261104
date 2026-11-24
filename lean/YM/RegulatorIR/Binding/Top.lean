import YM.RegulatorIR.Binding.Rafter

/-! At E empty, no Haar factor yet. Material for Fk top Wilson germ. Match
at each formal filtered operator before contour. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge}{f:Side}{I J L:Type}[Fintype I][Fintype J][Fintype L]
section Algebra
open Finset
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
def inscription (v:E→ℝ) (y:E) : PowerSeries ℝ:= PowerSeries.mk fun i=>jet v i y
def logread (v:E→ℝ) (y:E) : PowerSeries ℝ:= PowerSeries.mk fun i=>Series.Radial.layers v i y
lemma logbase (v:E→ℝ)(y:E): coeff 0 (logread v y)=0:=by simp [logread,Series.Radial.layers]
lemma prints (v k:E→ℝ)(y:E) : PowerSeries.mk (fun i=> Series.Radial.normTerm k v i y)= PowerSeries.C (Real.exp (-jet v 2 y)) * (inscription k y * expo (logread v y)):=by
 let p:=logread v y; let a:= Series.Radial.layers v
 have hm (i j:ℕ) : coeff j (p^i) = Zone.TaylorPow a i j y:= by
    induction i generalizing j with
    | zero =>simp only [pow_zero, PowerSeries.coeff_one, Zone.TaylorPow]
    | succ i ih=> rw [pow_succ,coeff_mul, Zone.TaylorPow]; unfold Zone.mul; apply Finset.sum_congr rfl;intro x _; rw [ih]; simp [a,p,logread]
 have ht (i:ℕ):coeff i (expo p)=expsum a i i y := by rw [expo, PowerSeries.coeff_mk, truncP,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [coeff_smul,hm]; rfl
 ext1 i; rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, normTerm]
 rw [mul_comm]; congr 1; unfold integrandSeries Zone.mul; rw [coeff_mul]; apply Finset.sum_congr rfl;intro j _; simp_rw [inscription,coeff_mk]; rw [show coeff j.2 (expo _)= _ from ht j.2]
lemma ink_one (x:E) : inscription (fun _=> (1:ℝ)) x=1:=by
 ext1 i; rw [coeff_one,inscription,coeff_mk]; by_cases h:i=0
 · subst i; simp
 rw [if_neg h,jet,iteratedFDeriv_const_of_ne h];simp
end Algebra

lemma integral_vacuous {K:Meadow G Empty→ℝ}: (∫ x, K x ∂tangent G Empty)=K 0 := by
 rw [Chart.tangent, Measure.pi_of_empty _ (0:Meadow G Empty), integral_dirac]
lemma hearsVac (F A:Hook G Empty I)(x:Meadow G I): manuscript F A x=PowerSeries.C (Real.exp (-jet (priceMap F) 2 (0,1,x))) * (inscription (priceMap A) (0,1,x)* expo (logread (priceMap F) (0,1,x))):=by
 rw [← prints, manuscript]; congr 1; ext i; unfold tomorrow rates;rw [integral_vacuous]; rw [show aura A=priceMap A from ?_]
 ext1 u; rw [aura, Chart.jacobian]; simp

-- typed leg alphabet; does not introduce a continuum projection
abbrev Book (G:Gauge)(f:Side) := Geometry.Hatch f G.ColorIndex
def tint (G:Gauge)(f:Side)(x:Horizon G f)(i : Book G f):ℝ:= (x i.1) i.2
def paw (B:Horizon G f→ℝ) : Medium G (OEdge f) (Book G f) := ⟨tint G f,B⟩

-- Top obligations. Are about insertion/log stencil evaluation only, on
-- unnormalized formal *analytic* seat, not after Wick. Require actual tapes.
structure Canvas (G:Gauge)(N:Scale)(T:Orders (Book G f))(A:Hook G Empty (OEdge f))(V:Orders (Book G f))(s m:ℕ):Prop where
 logA (y: Horizon G f) : flavor 2 (tint G f y) T= logread (priceMap (startO N)) (0,1,y)
 stencil (y:Horizon G f): PowerSeries.X ^s * flavor m (tint G f y) V= inscription (priceMap A) (0,1,y)
 vacuum : Vacuum T
 faces : gradedSymmetric T
 since : ∀ e, Within (e+m) (V e)
 align : gradedSymmetric V
variable {N : Scale}{T V: Orders (Book G f)} {A:Hook G Empty (OEdge f)}{s m:ℕ}
lemma Canvas.founds (Q:Canvas G N T A V s m): Dusk s (startO N) A (paw (G:=G) (f:=f) costO) T 1 V m:= by
 refine ⟨?_,?_,by norm_num, Q.vacuum,Q.faces,Q.since,Q.align⟩
 · intro y;rw [hearsVac]
   rw [start_color]; let k:=(paw costO (G:=G) (f:=f)).kinetic; change _ * (inscription (fun _:Meadow G Empty × ℝ × Meadow G (OEdge f)=>1) _ * _) = _ * _ * expo (flavor 2 (tint G f y) T)
   rw [ink_one,Q.logA,mul_one,one_mul]; rfl
 intro y; rw [hearsVac,hearsVac]; change _ * (inscription _ _ * _)= (_*(inscription (fun _:Meadow G Empty × ℝ × Horizon G f=>1) _*_) ) * PowerSeries.X^s * flavor m (tint G f y) _
 rw [ink_one, ← Q.stencil y];simp;ring
end YM.RegulatorIR.Binding
