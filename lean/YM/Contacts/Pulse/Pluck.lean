/- local Haar instances adapts the normalized Haar measure instances for UnitAddCircle from Mathlib/Analysis/Fourier/AddCircleMulti.lean for this project.
Authors: David Loeffler. Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache License 2.0. See NOTICE. -/

import YM.Contacts.Pulse.Shelf
/-! Fourier de-root on relative axes. Division factors with quantitative
 pre-scale cost. Layers is Stationary; we take transfer along identified
series at cover coefficients as a ledger split, not a finite-grid identity. -/
noncomputable section
namespace YM.Pulse.Spine
open Function Set Finset Filter Lattice RG Wilson Precision Stationary Exterior
open Bloch Laurent Push.AbsoluteSums Extra.Iteration MeasureTheory UnitAddTorus
open scoped Classical Topology BigOperators NNReal ENNReal
variable {α β X Y Z E : Type}{t n:ℕ}
section extract
variable [Fintype α]{f g:Shift α→ℂ}{η:ℝ≥0}{C D:ℝ}
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def torread (f: Shift α→ℂ) : C(Rim α,ℂ):= ∑' i, f i • mFourier i
lemma torread_cost (h: Width η C f): Summable (fun i=> f i • mFourier i):= Summable.of_norm (by simpa only [norm_smul,mFourier_norm,mul_one] using (h.unweighted η.property).2.1)
lemma torread_read (h: Width η C f) (x:Corn α): torread f (dress α x)= Laurent.read f (Laurent.walk α x) := by
  let A : C(Rim α,ℂ) →L[ℂ] ℂ:= ContinuousMap.evalCLM ℂ (Laurent.dress α x); change A _ = _
  unfold torread; rw [ContinuousLinearMap.map_tsum _ (torread_cost h)]; exact tsum_congr (fun i=> by rw [map_smul]; change f i*mFourier i _=mode _ i * f i; rw [wears,mul_comm])
lemma torread_basis (h: Width η C f) (i:Shift α): inner ℂ (mFourierLp 2 i) ((ContinuousMap.toLp 2 volume ℂ) (torread f))=f i := by
  let A:= innerSL ℂ (mFourierLp 2 i) ∘L ContinuousMap.toLp 2 (volume: Measure (Rim α)) ℂ
  change A _ = _; unfold torread; rw [ContinuousLinearMap.map_tsum _ (torread_cost h), tsum_eq_single i]; · rw [map_smul]; change f i * inner ℂ (mFourierLp 2 i) (mFourierLp 2 i)=_; simp only [orthonormal_iff_ite.mp orthonormal_mFourier,if_true,mul_one]
  intro x hx; rw [map_smul]; change f x * inner ℂ (mFourierLp 2 i) (mFourierLp 2 x)=0; rw [orthonormal_iff_ite.mp orthonormal_mFourier i x, if_neg hx.symm,mul_zero]
lemma tonify (hf: Width η C f)(hg:Width η D g)(h: ∀ p,Laurent.read f (axes p)= Laurent.read g (axes p)) : f=g:= by
  have hu : torread f = torread g := ContinuousMap.ext ( (fashion α).forall.mpr fun x=> by
    rw [torread_read hf,torread_read hg,show Laurent.walk α x=axes (fun i=>2*Real.pi*x i) by ext i; simp [Laurent.walk,axes]]; apply h)
  exact funext fun i=> by rw [← torread_basis hf, ← torread_basis hg,hu]
end extract
abbrev arc (i:α) : Shift α := Pi.single i 1
def ascend (i:α)(f: Shift α→E) (x:Shift α):= f (x-arc i)
section
variable [NormedAddCommGroup E]{σ η:ℝ≥0}{C D:ℝ}
def counter (i:α)(f: Shift α→E) := ascend i f - f
def torn {n:ℕ}(l: Fin n→α)(f: Shift α→E) : Shift α→E:= match n,l with
  | 0,_=> f
  | k+1,l=> counter (l 0) (torn (Fin.tail l) f)
@[simp] lemma torn_zero (l:Fin 0→α)(f:Shift α→E): torn l f=f:= by rw [torn]
@[simp] lemma torn_succ (l:Fin (n+1)→α)(f:Shift α→E): torn l f=counter (l 0) (torn (Fin.tail l) f):= by rw [torn]
variable [Fintype α]
lemma upward {f:Shift α→E}(i:α)(h:Width σ C f): Width σ (Real.exp σ*C) (ascend i f):= by
  refine budget_mono (budget_pull _ (show Injective (fun x:Shift α=>x-arc i) from fun p q h=> sub_left_inj.mp h) (budget_scale (x:=Real.exp σ) (by positivity) h)) (fun _=>by positivity) fun x=>?_
  rw [←mul_assoc,←Real.exp_add]; unfold ascend; gcongr
  have hl := size_add (arc i) (x-arc i); rw [add_sub_cancel _ x,show size (arc i)=1 by simp [size,arc,Pi.single_apply,apply_ite Int.natAbs]] at hl
  push_cast; apply le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hl) (show 0 ≤ (σ:ℝ) by positivity)); exact le_of_eq (by push_cast; ring)
lemma counter_cap {f:Shift α→E}(i:α)(h:Width σ C f): Width σ ((Real.exp σ+1)*C) (counter i f) := by
  rw [_root_.add_mul,one_mul]; refine budget_mono (budget_plus (upward i h) h) (fun _=> by positivity) fun p=> ?_
  rw [← mul_add]; gcongr; exact norm_sub_le ..
lemma tear_cap {f:Shift α→E} (h:Width η C f)(l: Fin n→α) : Width η ((Real.exp η+1)^n*C) (torn l f):= by
  induction n with | zero=> simpa using h | succ k IH=> rw [pow_succ',mul_assoc,torn_succ]; exact counter_cap _ (IH _)
end
section
variable [Fintype α]{σ η:ℝ≥0}{C D:ℝ}{f: Shift α→ℂ}
lemma divZ_step (i:α)(p: Laurent.Phase α): divZ i p=mode p (arc i)-1:= by simp [divZ,mode,arc,Pi.single_apply,mul_ite]
lemma counter_tone (h:Width η C f)(i:α){p:Laurent.Phase α}(hp:Within η p) : Laurent.read (counter i f) p= divZ i p * Laurent.read f p := by
  have he (k): mode p k • counter i f k=mode p k • ascend i f k-mode p k • f k:= smul_sub ..
  unfold Laurent.read; simp_rw [he]; rw [Summable.tsum_sub (( (upward i h).series p hp).2.1.of_norm) ((h.series p hp).2.1.of_norm),divZ_step,_root_.sub_mul,one_mul, ← tsum_mul_left]
  congr 1; rw [← Equiv.tsum_eq (Equiv.addRight (arc i))]; apply tsum_congr; intro j; simp only [ascend,Equiv.coe_addRight, mode_shift, add_sub_cancel_right, smul_eq_mul]; ring
lemma tear_tone (h: Width η C f)(l:Fin n→α){p:Laurent.Phase α}(hp:Within η p) : Laurent.read (torn l f) p= (∏ i : Fin n, divZ (l i) p) * Laurent.read f p:= by
  induction n with | zero=> simp | succ k IH=> rw [torn_succ,counter_tone (tear_cap h _) _ hp, Fin.prod_univ_succ,IH, mul_assoc]; rfl
end
lemma tear_real (l:Fin n→α)(g:Shift α→ℂ)(v:Shift α) : Complex.re (torn l g v) = torn l (Complex.re ∘ g) v:= by
  induction n generalizing v with | zero=> simp | succ k IH => simp only [torn_succ,counter,Pi.sub_apply,ascend,Complex.sub_re,IH]

variable {σ η:ℝ≥0}{C D:ℝ} {F: Shift (Keys t)→ℝ}
def pale (F:Shift (Keys t)→ℝ) : On (Keys t) ℂ := Complex.ofRealCLM ∘ F
lemma invest (h:Width η C F) : Width η C (pale F):= by simpa only [pale,Width,Function.comp_apply,Complex.ofRealCLM_apply, Complex.norm_real] using h
lemma liftoff {g:Shift (Keys t)→ℂ} (h: Width η C g) : Width η C (Complex.re ∘ g):= budget_mono h (fun _=> by positivity) fun i=> mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
lemma pry (σ:ℝ≥0)(t n:ℕ)(hs:0<σ) : ∃ η:ℝ≥0,0<η ∧ η≤σ ∧ ∃ K:ℝ,0≤K ∧ ∀ (C:ℝ)(F:Shift (Keys t)→ℝ), Width σ C F → Rays n (Laurent.read (pale F) ∘ axes) →
    ∃ G: (Fin n→Keys t)→Shift (Keys t)→ℝ, (∀ l,Width η (C*K) (G l)) ∧ F=∑ l,torn l (G l) := by
  obtain ⟨η,K,hη,he,hK,H⟩:= transfers n t (NNReal.coe_pos.mpr hs); lift η to ℝ≥0 using hη.le; refine ⟨η,NNReal.coe_pos.mp hη,NNReal.coe_le_coe.mp he,K,hK,fun C F h hp=> ?_⟩
  obtain ⟨G,hG,hu⟩:= H C (Cost.nonneg h) _ (Firm.of_series (invest h) (NNReal.coe_pos.mpr hs)) hp
  let f l:= torn l (G l); have hf l:= tear_cap (hG l) l
  have hx : Width η (∑ _l : Fin n→Keys t,(Real.exp η+1)^n*(C*K)) (fun p=>∑ l, f l p) := by
    refine budget_mono (budget_over Finset.univ (fun i p=> Real.exp (η*(size p:ℝ))* ‖f i p‖) _ (fun i _=> hf i)) (fun _=> by positivity) fun p=> ?_; rw [← mul_sum]; gcongr; exact norm_sum_le ..
  have hr := fun p => Firm.in_range (Firm.of_series (hx) hη) (axes_real p)
  have hm : pale F=fun p=> ∑ l,f l p := by
    refine tonify ((invest h).mono he le_rfl) hx fun p=> ?_
    have ht : Within η (axes p):= fun i=> (hr p i).le
    rw [hu (axes p) (hr p)]; unfold Laurent.read; simp_rw [Finset.smul_sum]
    rw [Summable.tsum_finsetSum (fun l _=> (((hf l).series (axes p) ht).2.1).of_norm)]; apply sum_congr rfl; intro i _; exact Eq.symm (tear_tone (hG _) i ht)
  refine ⟨fun i=> Complex.re ∘ G i,fun i=> liftoff (hG i),funext fun p=> ?_⟩
  have he := congr_arg Complex.re (congr_fun hm p); simp only [Complex.re_sum,pale,Function.comp_apply,Complex.ofRealCLM_apply,Complex.ofReal_re,f,tear_real] at he; simpa only [Finset.sum_apply] using he
end YM.Pulse.Spine
