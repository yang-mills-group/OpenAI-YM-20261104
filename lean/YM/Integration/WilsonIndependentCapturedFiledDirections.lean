import YM.Integration.WilsonIndependentCapturedAngularWinding
import YM.Next.WARD_BIN.Degree

/-! The factorial-normalized real directions used in the winding tariff
are exactly the ordered stored coefficients of the actual occupied
group polynomial. Repeated links use the same formula. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedFiledDirections
open Function Finset Lattice RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Diagram RegulatorIR.FVAAlt2 WilsonOriginalLinkedAngularPage
open WilsonIndependentCapturedAngularWinding
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {n : Side}
local notation "I" => SiteSlot G n
local notation "E" => Stationary.Link G n

open Tensor Analysis Work.G05 WardBin

private def plane (A : ∀ i : ℕ,Tensor.T (E) ℂ i) (n : ℕ) : (E)→ℂ := ∑ i ∈ Finset.range (n+1), diagonal (A i)
private lemma plane_smooth (A : ∀ i : ℕ,Tensor.T (E) ℂ i) (n : ℕ) (k : WithTop ℕ∞): ContDiff ℝ k (plane A n) := by
  rw [plane, show ∑ i∈Finset.range (n+1), diagonal (A i)=(fun x=>∑ i∈Finset.range (n+1), diagonal (A i) x) from funext fun x=> Finset.sum_apply ..]; exact ContDiff.sum (fun _ _=>diag_smooth _ _)

private lemma plane_coeff (A : ∀ i : ℕ,Tensor.T (E) ℂ i) (n : ℕ) {j : ℕ} (h : j≤n) (ha:Sym (A j)) : coeff (plane A n) j 0=A j := by
  apply ext_diag _ _ (coeff_symm (plane_smooth ..|>.contDiffAt)) ha
  funext x
  rw [← leading_tensor x (plane A n) (plane_smooth ..|>.contDiffAt)]
  rw [show (fun t:ℝ=> plane A n (t • x))=fun t:ℝ=>∑ i∈ Finset.range (n+1),t^i • diagonal (A i) x from funext fun _=> by rw [plane,Finset.sum_apply]; simp_rw [homogeneous]]
  rw [WardBin.lead_sum (f:=fun i (t:ℝ)=> t^i • diagonal (A i) x) (hf:=fun _ _=>by fun_prop)]
  simp_rw [lead_monomial]; exact Finset.sum_eq_single j (by intro a _ he; rw [if_neg he.symm]) (by simp [show j < n+1 by omega]) |>.trans (if_pos rfl)

def form {r : ℕ} (A : Packet (I) r) : Tensor.T (E) ℂ r :=
  ∑ z:Tuple (I) r, (A z:ℂ) •
    (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℂ).compContinuousLinearMap
      (fun j=>Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:(I)=>ℝ) (z j)))

theorem form_apply {r : ℕ} (A : Packet (I) r) (v : Fin r → (E)) :
    form A v = ∑ z:Tuple (I) r, (A z:ℂ) * ∏ j,(v j (z j):ℂ) := by
  simp [form,ContinuousMultilinearMap.mkPiAlgebra_apply]

private theorem symmetric {r : ℕ} {A : Packet (I) r} (sym : A.IsSym) : Tensor.Sym (form A) := by
  intro v e
  rw [form_apply,form_apply]
  apply Fintype.sum_equiv (Tuple.perm (I) e.symm)
  intro z
  change (A z:ℂ)*(∏ j,(v (e j) (z j):ℂ)) =
    (A (z ∘ e.symm):ℂ)*(∏ j,(v j (z (e.symm j)):ℂ))
  rw [sym e.symm z]
  congr 1
  simpa only [Equiv.symm_apply_apply] using Equiv.prod_comp e (fun j=>(v j (z (e.symm j)):ℂ))

theorem measured {r : ℕ} (T : Packet (I) r) (x : Tuple (I) r) :
    form T (fun j=>ray G (x j)) = (T x:ℂ) := by
  rw [form_apply,Finset.sum_eq_single x]
  · simp [WilsonOriginalLinkedAngularPage.ray]
  · intro z _ hz
    obtain ⟨j,diff⟩ := Function.ne_iff.mp hz
    have zero : ((ray G (x j) (z j):ℝ):ℂ)=0 := by simp [WilsonOriginalLinkedAngularPage.ray,diff]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) zero,mul_zero]
  · simp

def value (T : Ranked (I)) (k : ℕ) (v : E) : ℂ := ((MvPolynomial.eval v (packed T k):ℝ):ℂ)

private theorem polynomial (T : Ranked (I)) (k : ℕ) : value T k=plane (fun r=>form (T r)) k := by
  funext y
  simp [value,plane,packed,render,word,Tensor.diagonal,form_apply]

theorem angular {T : Ranked (I)} {r k : ℕ} (within : r ≤ k) (sym : (T r).IsSym)
    {F : E → ℂ} (group : ∀ u,F u=value T k u) (x : Tuple (I) r) :
    printed F x=T r x := by
  have field : F=plane (fun s=>form (T s)) k := (funext group).trans (polynomial T k)
  have jet : Tensor.coeff F r 0 = form (T r) := by
    rw [field]; exact plane_coeff _ _ within (symmetric sym)
  have actual := congrArg (fun h:Tensor.T (E) ℂ r => h (fun j=>ray G (x j))) jet
  have read : (r.factorial:ℝ)⁻¹ • WilsonOriginalLinkedAngularPage.coefficient r F x=(T r x:ℂ) :=
    actual.trans (measured _ _)
  have realRead := congrArg Complex.re read
  have paid : (r.factorial:ℝ)⁻¹ * (coefficient r F x).re=T r x := by
    simpa only [Complex.smul_re,smul_eq_mul,Complex.ofReal_re] using realRead
  exact (div_eq_inv_mul _ _).trans paid

open Marker Comparison.RG02 Comparison.RG02.Adjacent RegulatorIR.FVAAlt2.Sound
open RegulatorIR.FVAAlt2.Pipeline

theorem filed {L : Type} [DecidableEq L] (mask : Marker.Census L) (u : L) (toll e : ℕ)
    (clock : UnitCost) (V : Bulk.Colors mask G n) (bank : Orders (I)) {p : ℕ} (live : e ≤ p)
    (receipt : Booth.Arm.Single clock V bank u p toll) (r : ℕ) (x : Tuple (I) r) :
    printed (fun a=>See.noseC mask u clock V e (Stationary.arm G n 1 a)) x =
      WilsonPositionProgramCapturedWords.groupRows mask u toll e clock V r x := by
  rw [WilsonPositionProgramCapturedWords.single mask u toll e clock V bank live receipt]
  apply angular (k:=max (e+toll) r) (le_max_right _ _) (receipt.symmetricW e r)
  intro a
  have recorded : See.noseC mask u clock V e (Stationary.arm G n 1 a)=
      Booth.Uniforms.cuff bank toll e (Stationary.arm G n 1 a) := receipt.earned e live _
  rw [recorded,Booth.Uniforms.cuff,Binding.flavor_lo]
  unfold value
  rw [←pack_extends (receipt.grade e) (le_max_left (e+toll) r)]
  rfl

end YM.Integration.WilsonIndependentCapturedFiledDirections
