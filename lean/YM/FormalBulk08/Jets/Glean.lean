import YM.FormalBulk08.Jets.Lilt
import YM.FormalBulk08.Wick.Currents
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
Absolute Taylor stencils. `Rays` are real links at finite regulator (possibly extra
parameters). ContDiff∞ at the origin suffices; do not confuse these formal identities
with gates on jets through increasing horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Series Wick Function Filter Set Metric
open scoped Classical ContDiff Topology BigOperators
variable {I : Type*} [Fintype I]
abbrev Rays (I : Type*) := I → ℝ
def dotI (i : I) : Rays I := Pi.single i 1
def traceP (x : Rays I) (p : Glyphs ℝ I) := MvPolynomial.aeval x p

def laden (n : ℕ) (L : ContinuousMultilinearMap ℝ (fun _ : Fin n=>Rays I) ℝ) : Glyphs ℝ I :=
    ∑ m : Fin n → I,MvPolynomial.C (L (dotI ∘ m)) * ∏ i,MvPolynomial.X (m i)

def paste (f : Rays I→ℝ) : Plate ℝ I := PowerSeries.mk (fun n=> (n.factorial : ℝ)⁻¹ • laden n (iteratedFDeriv ℝ n f 0))
@[simp] lemma paste_coeff (f : Rays I→ℝ) (n) : PowerSeries.coeff n (paste f)= (n.factorial : ℝ)⁻¹ • laden n (iteratedFDeriv ℝ n f 0) := PowerSeries.coeff_mk ..

private lemma total_x (x : Rays I) : ∑ i,x i • dotI i=x := by ext i; simp [dotI,Pi.single_apply, mul_ite]
lemma trace_laden (x : Rays I) (n) (L : ContinuousMultilinearMap ℝ (fun _ : Fin n=> Rays I) ℝ) : traceP x (laden n L)=L (fun _=>x) := by
   conv_rhs => rw [← total_x x]
   unfold traceP laden; simp only [map_sum,_root_.map_mul,MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,map_prod,MvPolynomial.aeval_X]; rw [ContinuousMultilinearMap.map_sum] -- name
   simp_rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]; exact Finset.sum_congr rfl fun _ _=> mul_comm ..
lemma trace_paste (x : Rays I) (f : Rays I→ℝ) (n) : traceP x (PowerSeries.coeff n (paste f))=PertExtension.Series.Radial.jet f n x := by
   rw [paste_coeff, show ∀ c:ℝ,∀ p,traceP x (c•p)=c•traceP x p from fun c p => map_smul (MvPolynomial.aeval (R:=ℝ) _) c p, trace_laden]; rfl
omit [Fintype I] in
lemma orbit_ext {p q : Glyphs ℝ I} (h : ∀ x,traceP x p=traceP x q) : p=q := MvPolynomial.funext h
omit [Fintype I] in
lemma integral_ext {p q : Plate ℝ I} (h : ∀ x:Rays I,PowerSeries.map (MvPolynomial.aeval x).toRingHom p=PowerSeries.map (MvPolynomial.aeval x).toRingHom q) : p=q := by
  ext1 n; apply orbit_ext; intro x; have he := congr_arg (PowerSeries.coeff n) (h x); rw [PowerSeries.coeff_map,PowerSeries.coeff_map] at he; exact he
@[simp] lemma paste_first (f : Rays I→ℝ) : PowerSeries.coeff 0 (paste f)=MvPolynomial.C (f 0) := orbit_ext fun x=>by rw [trace_paste]; simp [traceP]

omit [Fintype I] in
private lemma rise_i {i : I} (p : Glyphs ℝ I) (x : Rays I) : HasDerivAt (fun r:ℝ=>traceP (x+r • dotI i) p) (traceP x (MvPolynomial.pderiv i p)) 0 := by
   induction p using MvPolynomial.induction_on with
   | C c=> simp [traceP,hasDerivAt_const]
   | add p q hp hq=> convert! hp.add hq using 1 <;> simp [traceP,Pi.add_def]
   | mul_X p j hp=>
      have h : HasDerivAt (fun r:ℝ=>traceP (x+r•dotI i) (MvPolynomial.X j)) (traceP x (MvPolynomial.pderiv i (MvPolynomial.X j))) 0 := by
        convert! (hasDerivAt_const (0:ℝ) (x j)).add ((hasDerivAt_id' (0:ℝ)).mul_const (dotI i j)) using 1
        · simp [traceP,Pi.add_def]
        simp [traceP,dotI, Pi.single_apply]
      convert! hp.mul h using 1 <;> simp [traceP,Pi.mul_def ] ; ring

/-- Formal gradient is actual coordinate Jacobian times formal g when applied to unshifted `paste`. -/
lemma gradient (f : Rays I→ℝ) (i : I) (hf : ContDiffAt ℝ ∞ f 0) : shaft (MvPolynomial.pderiv i) (paste f) = PowerSeries.X * paste (fun x=> fderiv ℝ f x (dotI i)) := by
   ext1 n; rw [coeff_shaft]
   rcases n with (_|n)
   · simp only [paste_first,MvPolynomial.pderiv_C, PowerSeries.coeff_zero_X_mul]
   rw [PowerSeries.coeff_succ_X_mul]
   apply orbit_ext; intro x
   have h1 := rise_i (i:=i) (PowerSeries.coeff (n+1) (paste f)) x
   simp_rw [trace_paste] at *
   let L := iteratedFDeriv ℝ (n+1) f 0
   let c : ℝ := ((n+1).factorial :ℝ)⁻¹
   have hx : HasDerivAt (fun r:ℝ=> (fun _ : Fin (n+1)=> x+r•dotI i)) (fun _=> dotI i) 0 := hasDerivAt_pi.mpr fun j => by simpa only [Pi.add_def,zero_add,one_smul] using! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id' (0:ℝ)).smul_const (dotI i))
   have hu : HasDerivAt (fun r:ℝ=> c * (L (fun _=>x+r•dotI i))) (c * ((L.linearDeriv (fun _=>x)) (fun _=>dotI i))) 0 := (by
      have hU := ((L.hasFDerivAt _).comp_hasDerivAt (0:ℝ) hx).const_mul c
      simpa using! hU)
   rw [HasDerivAt.unique h1 hu,ContinuousMultilinearMap.linearDeriv_apply]; unfold L
   have hc : ContDiffAt ℝ ((n+1:ℕ):WithTop ℕ∞) f 0 := hf.of_le (by exact WithTop.coe_le_coe.mpr le_top)
   simp_rw [cheek_pin f n 0 x (dotI i) _ hc]
   simp [c,PertExtension.Series.Radial.jet,Nat.factorial_succ];field_simp
end YM.FormalBulk08.Jets
