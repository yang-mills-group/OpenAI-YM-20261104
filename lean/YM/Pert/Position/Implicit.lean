import YM.Pert.Lattice.Bundles
import Mathlib.Analysis.Calculus.ImplicitContDiff
import YM.Work.G05.Taylor
/-!
# Analytic bookkeeping for a square position solve

At any fixed regulator, after stripping to numerical tested tensors, regard all square tests *as polynomial functions of a proposed frame* and linear in tested input arrays. We can use ordinary implicit function Taylor derivatives for the formal solve. This lemma isolates exactly the needed determinant (only at the leading **limiting** tensors) and convergence hypotheses. No assumptions on actual untested quantum laws give these conditions automatically.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Position
open Set Function Filter
open scoped Topology ContDiff BigOperators

section curve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Taylor data as a numerical polynomial *just for computing jets*. No Taylor-series convergence needed. -/
def curve (x : ℕ→E) (m : ℕ) (t : ℝ) : E := ∑ i ∈ Finset.range (m+1), t^i • x i
lemma curve_diff (x : ℕ→E) (m : ℕ) : ContDiff ℝ ω (curve x m) := by unfold curve; exact ContDiff.sum (fun i _ => (contDiff_id.pow i).smul contDiff_const)
lemma curve_zero (x : ℕ→E) (m : ℕ) : curve x m 0 = x 0 := by simp [curve,show ∀ i : ℕ, (0:ℝ)^i=if i=0 then 1 else 0 from fun i=> by by_cases h:i=0 <;> first | (exact Eq.trans (zero_pow h) (by rw [if_neg h])) | exact h.symm ▸ Eq.symm (if_pos rfl),ite_smul]
lemma curve_deriv (x : ℕ→E) {j m : ℕ} (hjm : j ≤ m) : iteratedDeriv j (curve x m) 0 = (j.factorial:ℝ) • x j := by
  unfold curve; rw [iteratedDeriv_fun_sum (fun i _ => ((contDiff_id.pow i).smul contDiff_const).contDiffAt)]
  simp_rw [show ∀ i, iteratedDeriv j (fun t : ℝ => t^i • x i) 0 = iteratedDeriv j (fun t : ℝ => t^i) 0 • x i from fun i=> iteratedDeriv_smul_const (by fun_prop) _, iteratedDeriv_fun_pow_zero]; simp [ite_smul,Finset.sum_ite_irrel,Finset.mem_range, Nat.lt_succ_of_le hjm]
lemma curve_fderiv (x : ℕ→E) {j p m : ℕ} (hj : j≤p) (hp : p≤m) : iteratedFDeriv ℝ j (curve x p) 0 = iteratedFDeriv ℝ j (curve x m) 0 := by simp_rw [iteratedFDeriv_eq_equiv_comp,comp_apply,curve_deriv x hj,curve_deriv x (hj.trans hp)]
end curve

section analytic
variable {A C Z V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Tested datum `x` of all determining equations, `z` for a reported functional of the frame. `n` is derivative order and `m` input truncation order. -/
def readJet (φ : A→V) (m n : ℕ) (W : C×V → Z) (x : ℕ→A) (z : ℕ→C) := iteratedDeriv n (fun t : ℝ => W (curve z m t, φ (curve x m t))) 0
private lemma composite_at (x : ℕ → C×A) (m) {w : C×A→Z} (hw : ContDiffAt ℝ ω w (x 0)) {j p} (hj : j ≤ p) (hp : p ≤ m) : iteratedDeriv j (w ∘ curve x m) 0 = iteratedDeriv j (w ∘ curve x p) 0 := by
  rw [iteratedDeriv_eq_equiv_comp, iteratedDeriv_eq_equiv_comp,comp_apply,comp_apply]; congr 1
  let H := ContDiffAt.of_le (m:=(↑p:WithTop ℕ∞)) hw (by exact le_top)
  apply Work.G05.jets_comp (d:=p) ((curve_diff x m).contDiffAt.of_le le_top) ((curve_diff x p).contDiffAt.of_le le_top) (by rwa [curve_zero]) (by rwa [curve_zero]) (by rw [curve_zero,curve_zero]) (fun k hk => (curve_fderiv x hk hp).symm) (fun _ _ => rfl) _ hj
private lemma zipped_path (x : ℕ→A) (z : ℕ→C) (m t) : curve (fun i=>(z i,x i)) m t=(curve z m t,curve x m t) := by simp [curve,Prod.smul_mk,Prod.fst_sum,Prod.snd_sum,Prod.ext_iff]
lemma read_together (φ : A→V) (x : ℕ→A) (z : ℕ→C) {m n p} (W : C × V→Z) (hw : ContDiffAt ℝ ω W (z 0, φ (x 0))) (hp : ContDiffAt ℝ ω φ (x 0)) (hn : n≤p) (hm : p≤m) : readJet φ m n W x z = readJet φ p n W x z := by
  unfold readJet
  simpa only [comp_def,zipped_path] using (composite_at (fun i => (z i,x i)) m (ContDiffAt.comp (g:=W) (f:=fun y => (y.1,φ y.2)) _ hw (contDiffAt_fst.prodMk (hp.comp (f:=Prod.snd) _ contDiffAt_snd))) hn hm)

lemma partial_right {f : A→ℝ→Z} (x : A) (n : ℕ) (h : ContDiffAt ℝ ω (uncurry f) (x,0)) : ContinuousAt (fun u => iteratedDeriv n (f u) 0) x := by
  have hd : ∀ n : ℕ, ContDiffAt ℝ ω (uncurry fun u => iteratedDeriv n (f u)) (x,0) := by
    intro k; induction k with
    | zero => simp [h]
    | succ k ih =>
      let K u := iteratedDeriv k (f u)
      simp_rw [iteratedDeriv_succ,uncurry_def]
      change ContDiffAt ℝ ω (fun p => fderiv ℝ (K p.1) p.2 1) (x,0)
      apply ContDiffAt.clm_apply (ContDiffAt.fderiv (n:=ω) (f:=fun p : A×ℝ => K p.1) (g:=Prod.snd) _ contDiffAt_snd (by simp)) contDiffAt_const
      exact ih.comp (f:=fun p : (A×ℝ)×ℝ => (p.1.1,p.2)) ((x,0),(0:ℝ)) (by fun_prop)
  exact (hd n).continuousAt.comp (f:=fun u : A => (u,(0:ℝ))) (by fun_prop)

lemma jets_limit {I : Type*} {l : Filter I} (D : ℕ→I→A) (x : ℕ→A) (hx : ∀ n : ℕ,Tendsto (D n) l (𝓝 (x n))) (m p : ℕ) (f : A→Z) (hf : ContDiffAt ℝ ω f (x 0)) :
    Tendsto (fun z : I => iteratedDeriv p (fun t : ℝ => f (curve (fun j=>D j z) m t)) 0) l (𝓝 (iteratedDeriv p (f ∘ curve x m) 0)) := by
  let y (k : I) (i : Fin (m+1)) := D i k
  let v : Fin (m+1) → A := fun i => x i.val
  have ht : Tendsto y l (𝓝 v) := tendsto_pi_nhds.mpr (fun j=> hx j.val)
  let K (u : Fin (m+1)→A) (t : ℝ) := ∑ i : Fin (m+1), t^(i.val) • u i
  have e (u : ℕ→A) (t : ℝ) : curve u m t=K (fun i => u i.val) t := by unfold curve K; rw [Finset.sum_range]
  have en : K v 0=x 0 := (e x 0).symm.trans (curve_zero x m)
  have he : ContDiffAt ℝ ω (uncurry (fun u : Fin (m+1)→A => fun t : ℝ => f (K u t))) (v,0):= ((show ContDiffAt ℝ ω f (K v 0) from en.symm ▸ hf).comp (f:=uncurry K) (v,0) (by unfold K uncurry; fun_prop))
  have hT := partial_right _ p he |>.tendsto.comp ht
  simpa [comp_def,e,K,y,v] using hT

lemma jets_join {I : Type*} {l : Filter I} {D : ℕ→I→A} {x : ℕ→A} (hD : ∀ n : ℕ,Tendsto (D n) l (𝓝 (x n))) {P : ℕ→I→C} {z : ℕ→C} (hP : ∀ n : ℕ,Tendsto (P n) l (𝓝 (z n))) (m p : ℕ) {φ : A→V} {W : C × V→Z} (hw : ContDiffAt ℝ ω W (z 0, φ (x 0))) (hp : ContDiffAt ℝ ω φ (x 0)) :
    Tendsto (fun k : I => readJet φ m p W (fun i => D i k) (fun i => P i k)) l (𝓝 (readJet φ m p W x z)) := by
  let f (u : C × A) := W (u.1,φ u.2)
  have hf : ContDiffAt ℝ ω f (z 0,x 0) := by
    apply ContDiffAt.comp (g:=W) (f:=fun y : C×A=>(y.1,φ y.2)) _ hw (contDiffAt_fst.prodMk (hp.comp (f:=Prod.snd) _ contDiffAt_snd))
  have ht := jets_limit (fun n k => (P n k,D n k)) (fun n => (z n,x n)) (fun n => (hP n).prodMk_nhds (hD n)) m p f hf
  simpa [comp_def,zipped_path,readJet,f] using ht
end analytic

section patches
variable {A V Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

structure Reports (f : A×V→Y) (x : A) (y : V) (φ : A → V) : Prop where
  fixes : φ x = y
  diff : ContDiffAt ℝ ω φ x
  curves : ∀ᶠ z in 𝓝 x, f (z,φ z)=f (x,y)
  strict : ∀ᶠ v in 𝓝 (x,y), f v=f (x,y) ↔ φ v.1=v.2
lemma Reports.of_square {f : A × V→Y} {x : A} {y : V} (hf : ContDiffAt ℝ ω f (x,y)) (hL : ((fderiv ℝ f (x,y)).comp (ContinuousLinearMap.inr ℝ A V)).IsInvertible) :
    ∃ φ : A → V, Reports f x y φ := ⟨hf.implicitFunction (by simp) hL, hf.implicitFunction_apply_self .., ContDiffAt.contDiffAt_implicitFunction hf (by simp) hL,hf.eventually_apply_implicitFunction .., hf.eventually_apply_eq_iff_implicitFunction ..⟩
lemma Reports.deletion {f : A×V→Y} {x : ℕ→A} {y} {φ} (h : Reports f (x 0) y φ) {I : Type*} {l : Filter I} {D : ℕ→I→A} (hD : Tendsto (D 0) l (𝓝 (x 0))) (m n : ℕ) : ∀ᶠ k in l, readJet φ m n f (fun i=>D i k) (fun i=>D i k) = iteratedDeriv n (fun _ : ℝ=>(f (x 0,y))) (0:ℝ) := by
  have hep (i : I) := curve_diff (fun j => D j i) m |>.continuous.tendsto (0:ℝ)
  simp only [curve_zero] at hep
  have h' : ∀ᶠ z in 𝓝 (x 0), ∀ᶠ v in 𝓝 z, f (v,φ v) = f (x 0,y) := eventually_eventually_nhds.mpr h.curves
  exact (hD.eventually h').mono (fun k hk => Filter.EventuallyEq.iteratedDeriv_eq n (hep k |>.eventually hk))
end patches
end YM.Pert.Position
