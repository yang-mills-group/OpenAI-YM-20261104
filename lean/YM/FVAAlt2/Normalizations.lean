import YM.FVAAlt2.Fold

/-!
# Evaluation of the PHYSICS moment at the actual Landau integration variables
This is at the bare coupling; actual parameter & field changes on every leg later.
All coefficient masks, action and partition function linked to actual lattice ones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Ends
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Book MS.Cylinder MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open scoped PowerSeries ContDiff
variable {G:Gauge}{n:Side}{ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ] (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))
set_option quotPrecheck false
local notation "𝑷"=> PowerSeries (Com (isOdd (ι:=ι) (κ:=κ)))
local notation "𝑩"=> PowerSeries (Bos ι)
local notation "f!"=>Com.forget (isOdd (ι:=ι) (κ:=κ))
local notation "p"=> isOdd (ι:=ι) (κ:=κ)
local notation "Λ"=>propagator (κ:=κ) A
local notation "T"=> PowerSeries ℂ
local notation "C"=> PowerSeries.C (R:=ℂ)
local notation "μ"=> chosen G n
local notation "m₀"=> (Bos.μC G n)
local notation "H"=> (radiant A b).map (Bos.upS (κ:=κ))
local notation "u"=> Bos.upS (κ:=κ) (ι:=ι)
set_option linter.unusedSectionVars false

lemma expense (x:𝑩): Glue.wick A (formExp (fixedAct A b)*u x) = Glue.wick A (u (effective A b*x)):= by
 let P:= priceMat A+hrMat A; let Z:= u P; let Y:𝑷:=∑ i:κ,Glue.debit H i; change Glue.wick A ( formExp ( Z+Y ) * u x)= _
 have ht(i j:κ): PowerSeries.constantCoeff (H i j)=0:= gravity0 A b i j
 have hx: PowerSeries.coeff 0 Z=0:=by unfold Z P Bos.upS; simp only [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,map_add,price0,hr0,add_zero,map_zero]
 have he: PowerSeries.coeff 0 Y=0:=by unfold Y; rw [map_sum]; exact sum_eq_zero fun i _=> Glue.debit0 _ ht i
 rw [Com.exponent_add hx he,mul_comm (formExp Z),mul_assoc,Glue.determinant_rule A H (fun i j k=>Bos.Silence _ i) ht _ (fun i=>?eba)]; unfold Z; rw [formExp_map]; -- assoc
 case eba=> unfold Z; rw [formExp_map]; exact Glue.Silent.mul (Bos.Silence _ _) (Bos.Silence _ _)
 have h: (1+H).det=u (1+radiant A b).det:= by rw [ RingHom.map_det, map_add,map_one ]; rfl
 unfold effective; rw [map_mul (u),map_mul (u), h, mul_assoc,mul_left_comm]

abbrev Xps := JetArray (Land G n)
def ray (Y:𝑩): Xps (G:=G) (n:=n):= fun x=> valS4 A x Y
lemma ray_const : ray A (1:𝑩)=1:= funext fun _=> map_one _
lemma ray_ready (x:𝑩): Pert.Orb.Ready (ray A x):= by
  intro k; unfold ray valS4; simp_rw [PowerSeries.coeff_map]; exact Bos.eval_budget A _

abbrev unpack (t:PowerSeries ℂ)(i:ℕ):=PowerSeries.coeff i t
lemma unpack_mul(x y:T): unpack (x*y)=Trunk.core (unpack x) (unpack y):= funext fun _=>PowerSeries.coeff_mul ..
lemma vacuum_cost : PowerSeries.constantCoeff (heart (chosen G n) (LAND (G:=G)) (fibers LAND LANDweight))≠0:=bowl_pos _ LAND_go (by simp [LANDweight,pane_flat]; change 0 < LinearMap.det (LinearMap.id (R:=ℝ) (M:= ↥(Flow G n))); rw [LinearMap.det_id]; exact one_pos)
lemma wick_upS(x:𝑩): Glue.wick (κ:=κ) A (u x)= unpack ( C m₀⁻¹ * Lam.heart μ LAND (ray A x)):=by
 rw [Bos.wick_up]; funext i; change Bos.Ω A _= PowerSeries.coeff i (C m₀⁻¹ * Lam.heart μ LAND (ray A x)); rw [PowerSeries.coeff_C_mul,Bos.wick_real,Lam.heart, PowerSeries.coeff_mk]; unfold Lam.Cost ray valS4; simp_rw [PowerSeries.coeff_map]; change _/ m₀=m₀⁻¹*_ ; rw [div_eq_mul_inv,mul_comm]; rfl

def Γprice (x:PowerSeries (Bos ι)): T:= C m₀⁻¹ * Lam.heart (E:=Land G n) (chosen G n) (LAND (G:=G) (n:=n)) ((fibers (E:=Land G n) (LAND (G:=G) (n:=n)) LANDweight)*ray A x) -- note shadow!!
lemma Wγ(x:𝑩): Glue.wick A (formExp (fixedAct A b)*u x)= unpack (Γprice A x):= by
 rw [expense,wick_upS]; unfold Γprice; congr 3; funext v; unfold ray; rw [map_mul, valuation_body]; rfl

lemma numγ (hn:Admissible n) (x:𝑩): ℶV Λ
    ((PermV p).core (exp0 p (pullSeries (embeddingM A b) (posEnergy (Wilsonian.core G) n true))) (f! (u x))) = unpack (Γprice A x):= by rw [installedE A b hn,←Com.forget_exp,←Com.forget_mul]; exact Wγ A b x
lemma vacγ (hn:Admissible n): ℶV Λ (exp0 p (pullSeries (embeddingM A b) (posEnergy (Wilsonian.core G) n true)))=unpack (Γprice A 1):=by have h:=numγ A b hn 1; rw [map_one,Com.forget_one,(PermV p).identityR] at h; exact h

lemma bare_points (hn:Admissible n)(x:𝑩): Endμ Λ p (pullSeries (embeddingM A b) (posEnergy (Wilsonian.core G) n true)) (f! (u x)) (unpack (Lentry (ray A x))) := by
 unfold Endμ; rw [numγ A b hn,vacγ A b hn,← unpack_mul]; unfold Γprice Lentry Lam.choir; rw [ray_const,mul_one]; apply congrArg unpack; -- ring
 rw [mul_assoc, mul_left_comm (Lam.heart μ LAND (fibers LAND LANDweight)), PowerSeries.mul_inv_cancel _ (vacuum_cost (G:=G) (n:=n)),mul_one]

end YM.FVAAlt2.Ends
