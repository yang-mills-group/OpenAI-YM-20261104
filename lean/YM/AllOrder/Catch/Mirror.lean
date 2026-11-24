import YM.AllOrder.Catch.Moon
import YM.AllOrder.Laplace.Native
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
variable {ι:Type}[Fintype ι][DecidableEq ι]
local notation "Y"=> Body ι
local notation "Ω"=> ℝ×(X×Y)
variable (V:ℝ× (X× Body ι)→ℝ) (W:X) {n:ℕ}
    {A B: X× Body ι→ℝ}{M:X→ Matrix ι ι ℝ}{ρ:X→Body ι}
    (h:Accent A B M ρ)
local notation "T"=> course W
local notation "W₀"=> ρ∘ course W
variable (R:ℝ) (r:ℝ) (hr:0< Laplace.curvature A (fderiv ℝ (course W) 0 1) (fderiv ℝ (ρ ∘ course W) 0 1)+r)
variable (hp:Rise V)
local notation "Q"=> prepare ((A∘Prod.snd)+V) (course W) (ρ∘course W) r
set_option quotPrecheck false
local notation "Hi"=> fun p:Ω=> R*Real.exp (-B p.2)
local notation "Ψ"=> (Hi)∘ tone (course W) W₀
local notation "S"=> Real.exp ∘ slopeP (course W) A B M ρ
local notation "α"=> Real.exp (-r)*R*munit (M 0)
local notation "J"=> Shield.lens₀ (M 0)⁻¹
local notation "g"=> unroll (A:=A) (B:=B) (M:=M) (ρ:=ρ) (V:=V) (W:=W)
include hr hp h
local notation "μ"=> sweep (M 0)⁻¹
def coin (i:ℕ):=∫ y, someJ (g y) i ∂μ
local notation "Ξ"=> coin V W (A:=A) (B:=B) (M:=M) (ρ:=ρ)
variable (hR:0<R)
lemma tally (he:∀ i≤n,Integrable (fun y=> someJ (g y) i) (μ)): ∀ i ≤ n, Laplace.part volume Q Ψ i= α • (plus (someJ S) (Ξ) i):= by
 intro i hi; let G z:= plus (someJ S) (someJ (g z)) i
 unfold Laplace.part; simp_rw [show ∀ z:Y,normTerm Ψ Q i (onLane z)= α * (J z * G z) from fun z=>(congr_fun (melt W h hp R r hr z) i).trans (mul_assoc ..), integral_const_mul]; rw [← Shield.recommends (M 0)⁻¹ h.station.self_of_nhds.1.inv G]; rw [smul_eq_mul]; apply congr_arg (α * ·)
 unfold G plus Tested.conv Tested.term; simp_rw [PowerSeries.coeff_mul,PowerSeries.coeff_mk]; rw [integral_finsetSum]; swap; · exact fun j hj=> (he j.2 (by have hh:= Finset.HasAntidiagonal.mem_antidiagonal.mp hj; omega)).const_mul _
 simp_rw [integral_const_mul]; rfl -- checkpoint
include hR
lemma receives (he:∀ i≤n,Integrable (fun y=>someJ (g y) i) (μ)): logS (Real.exp r • Laplace.part volume Q Ψ) n = just (Real.log (R*munit (M 0))) n + someJ (slopeP (course W) A B M ρ) n + logS (Ξ) n:=by
   have ht := nice_slope h _ (course_claim h W).cont (course_claim h W).p0; let s:=plus (someJ S) Ξ; have hS :0< someJ S 0:=by rw [someJ_zero]; exact Real.exp_pos _
   have hw(i:Y): someJ (g i) 0=1:= by rw [someJ_zero]; unfold unroll Function.comp; rw [Catch.initial h hp,Real.exp_zero]
   have hω :0 < Ξ 0:= by unfold coin; simp_rw [hw]; simp
   have hs':0<s 0:=by simpa [s,plus,Tested.conv,Tested.term,PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.constantCoeff_mk] using mul_pos hS hω
   have hs:0<R*munit (M 0):= mul_pos hR (munit_pos (M 0))
   let v:= Real.exp r • Laplace.part volume Q Ψ; let u:= (R*munit (M 0)) • s; have hv:delay v n=delay u n:= by
       funext i; refine Finset.sum_congr rfl fun k hk=> ?_; apply congr_arg; unfold v u s; rw [Pi.smul_apply,Pi.smul_apply, tally V W h R r hr hp he k (by rw [mem_range] at hk; omega), smul_smul,show Real.exp r * α=R*munit (M 0) from (by rw [Real.exp_neg, ← mul_assoc (Real.exp r), mul_inv_cancel_left₀ (Real.exp_pos r).ne'])]
   rw [show logS v n=logS ((R*munit (M 0)) • s) n from congr_arg (fun p=> someJ (Real.log ∘ p) n) hv,← exact_scale, log_mash (show 0<just _ 0 from hs) hs',log_const _ hs]; unfold s; rw [log_mash hS hω, conviction ht,log_expS]; dsimp only [Pi.add_apply]; ring
lemma accessible (k:ℕ) : Measurable (fun x=>someJ (g x) k):= by
 induction k using Nat.strong_induction_on with
 | h k ih=>
    let F j x:= someJ (g x) j; let L x:= plus (someJ S) (someJ (g x)) k; let f:= someJ S
    have he : Measurable L:= by
       let u x:= normTerm Ψ Q k (onLane x); let A' x:= α * J x; have hμ (x:Y):0<A' x:= mul_pos (mul_pos (mul_pos (Real.exp_pos _) hR) (munit_pos _)) (Shield.fullFuel _ x); have hz : Measurable u:= ((Smooth.continuousTerms Ψ Q k).comp (f:=onLane) (show Continuous (onLane («Y»:=Y)) from continuous_const.prodMk continuous_id)).measurable -- type name
       rw [show L=(fun x=> u x/A' x) from funext fun x=>Eq.symm ((div_eq_iff (hμ x).ne').2 ((congr_fun (melt W h hp R r hr x) k).trans (mul_comm ..)))]; exact Measurable.div hz (measurable_const.mul (Shield.bulbB («S»:=fun _=> (M 0)⁻¹) (fun i j=> measurable_const) measurable_id))
    let s:= Finset.range k; let Z x:= ∑ i∈s,f (i+1)*F (k-(i+1)) x; have hω:0< f 0:= by unfold f; rw [someJ_zero]; exact Real.exp_pos _
    change Measurable (F k); rw [show F k=(fun x=>(L x-Z x)/ f 0) from ?_]; swap; · funext x; apply Eq.symm ((div_eq_iff hω.ne').mpr ?_); unfold L plus Tested.conv Tested.term Z; simp_rw [PowerSeries.coeff_mul,PowerSeries.coeff_mk]; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> someJ S i * someJ (g x) j) k,Finset.sum_range_succ',Nat.sub_zero]; change (_+ f 0 * F k x)-_= _; unfold s; dsimp only [F,f]; ring
    let hh:Measurable Z:= by apply Finset.measurable_sum s; intro i hi; exact measurable_const.mul (ih (k-(i+1)) (by have hh:=mem_range.mp hi; omega));
    exact (he.sub hh).div_const _
end YM.AllOrder.Catch
