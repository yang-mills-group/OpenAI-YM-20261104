import YM.FormalBulk08.Jets.Knobs

/-!
Composition of rescaled-chart Taylor stencils and Jacobian. Physical scales not
substituted into these functions. This is the transfer packet before choosing G.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Jets
open Series Wick PowerSeries Function Filter Set Metric
open scoped BigOperators ContDiff Topology Classical
open PertExtension.Series Tested
variable {I V R : Type*} [CommRing R]

def afterX (p : PowerSeries R) (n : ℕ) : PowerSeries R := mk fun i=> coeff (n+i) p
@[simp] lemma after_one (p : PowerSeries R) (n i : ℕ) : coeff i (afterX p n)= coeff (n+i) p := coeff_mk ..
lemma after_rope (p : PowerSeries R) (n : ℕ) (h : ∀ i<n,coeff i p=0) : X^n * afterX p n=p := by
   ext1 i; rw [coeff_X_pow_mul']; split_ifs with hi
   · rw [after_one,Nat.add_sub_of_le hi] -- name
   exact (h _ (Nat.lt_of_not_ge hi)).symm
lemma gaze_cut (f : ℝ→ℝ) (p : PowerSeries ℝ) (hp : gaze f p) (n : ℕ) (h : ∀ i<n, coeff i p=0) : gaze (fun r => (r⁻¹)^n * f r) (afterX p n) := by
   unfold gaze term; simp_rw [after_one]; exact Aspiration.shift hp h
lemma after_move (x : Rays I) (p : Plate ℝ I) (n) : glimpse x (afterX p n)= afterX (glimpse x p) n := by ext1 i; simp [glimpse]
variable [Fintype I]
lemma paste_sum (f g : Rays I→ℝ) (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) : paste (f+g)=paste f+paste g := photo fun x=> unique_gaze (fixed_path x (f+g) (hf.add hg)) (by rw [map_add]; exact gaze_plus (fixed_path x f hf) (fixed_path x g hg))
lemma paste_turn (f : Rays I→ℝ) (h : ContDiffAt ℝ ∞ f 0) : paste (-f)= -paste f := photo fun x=> unique_gaze (fixed_path x (-f) h.neg) (by rw [map_neg]; exact gaze_neg (fixed_path x f h))
lemma paste_mul (f g : Rays I→ℝ) (hf : ContDiffAt ℝ ∞ f 0) (hg : ContDiffAt ℝ ∞ g 0) : paste (f*g)=paste f*paste g := photo fun x=> unique_gaze (fixed_path x (f*g) (hf.mul hg)) (by rw [map_mul]; exact gaze_fade (fixed_path x f hf) (fixed_path x g hg))
lemma paste_flat (a : ℝ) : paste (fun _ : Rays I => a)=C (MvPolynomial.C a) := by
   apply photo; intro x; have h : glimpse x (C (MvPolynomial.C a))=C a := by simp [glimpse]
   rw [h]; exact unique_gaze (fixed_path x _ contDiffAt_const) (gaze_exact a)
lemma paste_replace {f g:Rays I→ℝ} (h : f=ᶠ[𝓝 0] g) : paste f=paste g := by
   ext1 i; rw [paste_coeff,paste_coeff,(h.iteratedFDeriv ℝ i).eq_of_nhds]

variable [Fintype V]
/-- Input type I and output type V. -/
def motor (h : Rays I→ Rays V) : V → Plate ℝ I := fun i=> afterX (paste fun x=>h x i) 1
omit [Fintype V] in
lemma town (u : Rays I→ Rays V) (i:V) (h : u 0=0) : X * motor u i=paste (fun x=> u x i) := by apply (by simpa [motor] using! after_rope (paste (fun x=>u x i)) 1 (fun j hj=> by rw [Nat.lt_one_iff.mp hj,paste_first,h,Pi.zero_apply,map_zero] ))
lemma paste_steps (u : Rays V→ℝ) (f : Rays I→ Rays V) (hu : ContDiffAt ℝ ∞ u 0) (hf : ContDiffAt ℝ ∞ f 0) (h : f 0=0) : paste (u ∘ f)=roam ℝ (motor f) (paste u) := by
   apply photo; intro x;rw [glimpse_slide]
   have hz : ContDiffAt ℝ ∞ u (f 0) := by rw [h]; exact hu
   refine unique_gaze (fixed_path x _ (hz.comp 0 hf)) ?_
   let y : ℝ → Rays V := fun r => r⁻¹ • f (r • x)
   have hc (i : V) : gaze (fun r=> y r i) (glimpse x (motor f i)) := by
      rw [motor, after_move]
      have hp := gaze_cut (f:=fun r=> f (r•x) i) _ (fixed_path x _ (show ContDiffAt ℝ ∞ (fun a => f a i) 0 by fun_prop)) 1 (fun i hi=> by rw [Nat.lt_one_iff.mp hi,glimpse_coeff,paste_first]; simp [h,traceP])
      simpa only [y, pow_one,Pi.smul_apply,smul_eq_mul] using! hp
   have hx:= fitted_path y _ u hu hc
   refine gaze_replace hx (eventually_pos.mono fun r hr=>?_); simp [y,comp,smul_smul,hr.ne']
lemma coord_diff (u : Rays I→ Rays V) (hu : ContDiffAt ℝ ∞ u 0) (i : V) : ContDiffAt ℝ ∞ (fun x=>u x i) 0 := by fun_prop

lemma motor_diff (u : Rays I → Rays V) (h : u 0=0) (hu : ContDiffAt ℝ ∞ u 0) (j : I) (i : V) : shaft (MvPolynomial.pderiv j) (motor u i)=paste (fun x=>fderiv ℝ (fun x=>u x i) x (dotI j)) := by
   have hh:= gradient (fun x=> u x i) j (coord_diff _ hu _)
   rw [←town u i h,Derivation.leibniz,shaft_X,smul_zero,add_zero,smul_eq_mul] at hh
   ext1 n; have he := congr_arg (coeff (n+1)) hh; rw [coeff_succ_X_mul,coeff_succ_X_mul] at he; exact he
end YM.FormalBulk08.Jets
