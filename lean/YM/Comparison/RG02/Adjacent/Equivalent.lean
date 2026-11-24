import YM.Comparison.RG02.Adjacent.Sale
/-!
# Tensor-angle turn and its inverse

Sale of a polynomial ranked program recovers order≤r regular coefficients **exact**;
Use `curvedAt` for Ward along log-field coordinates, no numeric budget claim.
For carrying W across one step use `barter` on formal graded/log board (binomial marker
algebra Order.*); for runtime bounds need additional COST on Taylor tails and rematching β.
No complex β used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice Marker Multi
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "φ"=> 𝓝 (0:ℝ)
local notation "λ₀"=> (ω:WithTop ℕ∞)
variable {U : Display X} {K L : UnitCost} (d:ℤ) (r:ℕ) {m:ℕ→ℤ} (hu:Charge r m U)
local notation "α"=> born U K d r
local notation "F"=> K.rating
local notation "H"=> L.rating
include hu
lemma affordable (K:UnitCost) (h:Monotone m): Charge r m (born U K d r):= fun i hi=> apportion K d r hu i hi fun _ hh=> h hh.le
lemma curvedAt (K:UnitCost) (a:ℝ→X)(hp : ContDiffAt ℝ ω a 0) : Shadow r (fun t=> cover (born U K d r) r t (a t)) (fun t=> ages U d r t (K.rating t) (a t)) := by
   simp_rw [reference K d r hu,quoted d r hu]; exact Shadow.sum (range (r+1)) fun j hj=> Shadow.sum _ fun i hi=>
      ((Shadow.truncate r (monetized K d j i)).symm).product (Shadow.refl ((levelJet (f:=U j) (hu j (mem_range_succ_iff.mp hj)).smooth.contDiffAt i).smooth.contDiffAt.comp _ hp))
lemma buying (L:UnitCost) (a:ℝ→X)(he:ContDiffAt ℝ ω a 0): ContDiffAt ℝ ω (fun t=> cover U r (L.enter t) (a t)) 0 := by unfold cover; apply ContDiffAt.sum; intro i hi; exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ L.here).pow _).mul ((hu i (mem_range_succ_iff.mp hi)).smooth.contDiffAt.comp _ he)
lemma reverse (hc : K.Recurs L)(i:ℕ)(hi:i≤r) : born (born U K d r) L d r i=U i:= by
   funext x
   let e : ℝ→X:= fun t=> F t • x
   let a : ℝ→ℂ:= fun t=> ↑( H t ^ d)
   have hz : Shadow r (fun t=> a t*cover α r (L.enter t) (e (L.enter t))) (fun t=> a t*ages U d r (L.enter t) (F (L.enter t)) (e (L.enter t))) := by
      have ha : ContDiffAt ℝ ω a 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (L.spin d)
      have he : ContDiffAt ℝ ω e 0:= K.smooth.smul contDiffAt_const
      exact (Shadow.refl ha).product ((curvedAt d r hu K e he).respite L)
   have hz' : (fun t=> ages α d r t (H t) x) =ᶠ[φ] fun t=> a t*cover α r (L.enter t) (e (L.enter t)) := (hc.symm.stays).mono fun t ht=> by unfold ages e UnitCost.enter at *; simp only [ht]; rfl
   have hv : (fun t=> a t*ages U d r (L.enter t) (F (L.enter t)) (e (L.enter t)))=ᶠ[φ] fun t=> peval (fun j=> U j x) r t := by
      filter_upwards [hc.symm.stays, L.roots.eventually K.bright,L.bright,hc.stairs] with t ht hh hv hx
      unfold ages UnitCost.enter at *
      unfold a e; simp only [Function.comp_apply,id_eq] at *
      -- hx : whole product
      rw [hx,ht,smul_smul, inv_inv,mul_inv_cancel₀ hv.ne',one_smul, inv_zpow, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (zpow_ne_zero _ hv.ne'), Complex.ofReal_one,one_mul]; simp_rw [cover,peval,Zone.eval,Complex.real_smul, Complex.ofReal_pow]
   calc
     _ = motion (fun t=> a t * cover α r (L.enter t) (e (L.enter t))) i := mgerm hz'
     _ = motion _ _ := hz.aligns i hi
     _ = _ := (mgerm hv).trans ((polary _ i r).trans (if_pos hi))
end YM.Comparison.RG02.Adjacent
