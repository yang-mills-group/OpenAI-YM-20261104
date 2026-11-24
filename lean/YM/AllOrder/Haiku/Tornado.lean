import YM.AllOrder.Haiku.Tip
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Coat
open Work.F05 PertExtension.Series Radial Bloch
variable (p:Clip)(V:PathData G)(b:ℝ){Λ:ℝ} (h:V.Bounds p a C Λ)
include h
lemma shore (n:Side): Stationary.Pointwise (mainTerm p V ∘ input G n) ∧ Stationary.Pointwise (summer p V b n∘ input G n):= by
 let hx:=stain_knit (m:=n) _ _ h; have he: (mainTerm p V ∘ input G n)=inputSeries p V+turnSeries V.cubic+turnSeries V.quartic:= intent ..; exact ⟨he.symm ▸ (hx.add (stain_ink V.cubic h.width h.three fun i=>(h.invariant i).2.1)).add (stain_ink V.quartic h.width h.four fun i=>(h.invariant i).2.2), (hx.coin b).add (stain_ink V.loop h.width h.two fun i=>(h.invariant i).1)⟩
lemma presentable (j:ℕ)(m:Side) : Stained G (Stipend p V b j m):= by
 intro u; let v : Link G m→L[ℝ] Link G m:= stain u
 let f i:= input G m i; let B:= mainTerm p V ∘ f; let C':= summer p V b m ∘ f; let hZ:= shore p V b h m
 have hh(f: F[m]→ℝ)(hf:Stationary.Pointwise f)(k:ℕ): (jet f k) ∘ v = jet f k:= by
    have he:= ((hf.stained u).iteratedFDeriv ℝ k).self_of_nhds; funext x; unfold jet; simp only [Function.comp_apply]; apply congr_arg; apply Eq.trans (b:= iteratedFDeriv ℝ k (f ∘ v) 0 (fun _=>x)) _ (congr_arg (fun g:Tensor.T (Link G m) ℝ k=> g (fun _=>x)) he); rw [Next.Foundations.jets_linear _ hf.analytic.contDiffAt,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 apply Eventually.of_forall; intro x; exact congr_arg₂ (·+·) (congr_fun (hh B hZ.1 (j+2)) x) (congr_fun (hh C' hZ.2 j) x)
open Further.PhysicalPeriodLimitF933 Shingle Macrame
omit h in
lemma owes (W:Macrame.Window n m k) (x:Config G n): summer p V b m (W.links x)= (k:ℝ)*summer p V b n x:= by
 unfold summer Precision.secondTerm Precision.loop Patch.average; simp_rw [W.signed, Macrame.Window.quadratic_price, Macrame.Window.unc, ← Finset.mul_sum]; ring

lemma stamina (W:Macrame.Window n m k) (j:ℕ)(x:Link G n): Stipend p V b j m (convey W x)=(k:ℝ)* Stipend p V b j n x:= by
 let A(c:Side):= mainTerm p V ∘ input G c; let B(c:Side):= summer p V b c ∘ input G c; let U:=convey W (α:=L)
 have ht f g (hf:ContDiffAt ℝ ω f 0)(hg:ContDiffAt ℝ ω g 0)(h:f ∘ U= (k:ℝ) • g) (j:ℕ): jet f j (U x)=(k:ℝ)*jet g j x:= by
    unfold jet; rw [show iteratedFDeriv ℝ j f 0 (fun _=> U x)= iteratedFDeriv ℝ j (f ∘ U) 0 (fun _=>x) from ?_,h,iteratedFDeriv_const_smul_apply (hg.of_le le_top),_root_.smul_apply,smul_eq_mul]; · ring
    rw [Next.Foundations.jets_linear _ (hf.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply]
 change jet _ (j+2) _+jet _ j _ = _ *( _+ _); rw [mul_add]; apply congr_arg₂ (·+·) (ht _ (A n) (shore p V b h _).1.analytic.contDiffAt (shore p V b h _).1.analytic.contDiffAt ?_ _) (ht _ (B n) (shore p V b h _).2.analytic.contDiffAt (shore p V b h _).2.analytic.contDiffAt ?_ _)
 · exact funext fun x'=> (congr_arg (mainTerm p V) (billing W x')).trans (W.revenue p V _)
 exact funext fun x'=> (congr_arg (summer p V b m) (billing W x')).trans (owes ..)
end Coat
end YM.AllOrder.Haiku
