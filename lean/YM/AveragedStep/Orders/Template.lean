import YM.AveragedStep.Parcel.Plea
import YM.PertExtension.Uniform
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Precision MeasureTheory Function Filter Tree Loops Wilson Set Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal Classical ContDiff
open YM.PertExtension.Series.Radial
section general
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
lemma radial_jet (f:X→ℝ)(n:ℕ):ContDiff ℝ 1 (jet f n):= by
  let t:=iteratedFDeriv ℝ n f 0
  have h: ContDiff ℝ 1 (fun x:X=>t fun _=>x):=t.contDiff.comp (g:=t) (contDiff_pi.mpr (fun i=>contDiff_id)) -- g param
  exact contDiff_const.mul h
lemma charged (f:X→ℝ)(n:ℕ):∃ C:ℝ,0≤C ∧ ∀ v,|jet f n v|≤C*‖v‖^n := by
  let t:=iteratedFDeriv ℝ n f 0
  let k:ℝ := (n.factorial:ℝ)⁻¹
  have hk : 0 ≤ k := by unfold k; positivity
  refine ⟨k*‖t‖,by positivity,fun v=>?_⟩
  change |k*t _| ≤ _; rw [abs_mul, abs_of_nonneg hk,mul_assoc]; gcongr
  simpa using t.le_opNorm (fun _=>v)
lemma ticketSum (f:X→ℝ)(n:ℕ):∃ C:ℝ,0≤C∧∀ v, (∑ i∈Finset.range (n+1),|jet f i v|) ≤ C*(1+‖v‖)^n := by
  choose C hC H using (fun i=> charged f i)
  refine ⟨∑ i∈Finset.range (n+1),C i,by exact Finset.sum_nonneg fun i _=> hC _,fun v=>?_⟩
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro i hi; exact (H i v).trans (mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖v‖≤1+‖v‖) _).trans (pow_le_pow_right₀ (by simp) (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))) (hC i))
variable [FiniteDimensional ℝ X]
lemma radial_collar {f:X→ℝ}{r:ℝ}(hr:0<r)(hf:∀ x∈closedBall 0 r,ContDiffAt ℝ ∞ f x)(n:ℕ):∃ C:ℝ, 0≤C∧∀ (v:X)(τ:ℝ), 0<τ → ‖τ • v‖ ≤ r →
   |f (τ • v)- ∑ i∈Finset.range (n+1),τ^i*jet f i v| ≤ C * τ^(n+1)*‖v‖^(n+1):=by
  let s:=closedBall (0:X) r
  let g(x:X):= f x -∑ i∈Finset.range (n+1),jet f i x
  have hg:ContinuousOn g s:= (ContinuousOn.sub (f:=f) (s:=s) (g:=fun x=>∑ i∈Finset.range (n+1),jet f i x) (fun x hx=>(hf x hx).continuousAt.continuousWithinAt)) (continuousOn_finsetSum _ (fun i _=> (radial_jet f i).continuous.continuousOn))
  obtain ⟨B,H⟩:=isCompact_closedBall (0:X) r |>.exists_bound_of_continuousOn hg
  obtain ⟨δ,C,hδ,hC,h⟩:=deposition f n (hf _ (mem_closedBall_self hr.le))
  refine ⟨max C (B*δ⁻¹^(n+1)),hC.trans (le_max_left ..),fun v t ht hh=>?_⟩
  rw [norm_smul_of_nonneg ht.le] at hh
  let k:=n+1
  by_cases he:t*‖v‖≤δ
  · have hl:=h v t ht he
    change |f (t • v)-∑ i∈Finset.range (n+1), t^i*jet f i v|≤ _ at hl
    refine hl.trans ?_
    rw [mul_right_comm _ (‖v‖^_)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) (by positivity)
  have hw:= H _ (show t • v∈s from by rw [mem_closedBall_zero_iff,norm_smul_of_nonneg ht.le]; exact hh)
  unfold g at hw; simp_rw [jet_smul] at hw
  refine hw.trans ?_
  have hK:0≤B:= (norm_nonneg _).trans hw
  have hZ: 1≤ δ⁻¹^k * (t^k*‖v‖^k):=by rw [←mul_pow,←mul_pow]; exact one_le_pow₀ (by rw [←div_eq_inv_mul,le_div_iff₀ hδ]; linarith)
  calc
    _ ≤ (B*δ⁻¹^k)*t^k*‖v‖^k:=by rw [mul_assoc,mul_assoc B,← mul_assoc (δ⁻¹^k)]; exact le_mul_of_one_le_right hK (by rw [mul_assoc]; exact hZ)
    _ ≤ _:=by gcongr; exact le_max_right ..
end general

variable {G:Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}(Q:Cuff P K A)
-- NOTE formal jets DO NOT depend on gate threshold Q.width. Branch only
-- used for analytic estimates with the physical product; kernels use
-- trivial chart continuum tensors aliged with the given A convention.
def tooth (P:Patch)(t:Mold)(i:Vectors P G) (n:ℕ) := jet (fun y=> fderiv ℝ (chip P K t (canon P)) y i) n
def gum (A:ChartRatio G)(v:G.Color)(n:ℕ):= jet (fun y=> Cuff.haarScore (A:=A) y v) n
lemma first_w {P:Patch} {K:KernelChoices}(hb:P.Branches K G)(t:Mold)(i:Vectors P G):
    tooth (K:=K) P t i 0 = fun _=>0:=by
 funext j; unfold tooth; rw [jet_zero]
 suffices hv:IsLocalMin (chip P K t (canon P) (G:=G)) 0 by rw [hv.fderiv_eq_zero,zero_apply]
 refine Eventually.of_forall (p:=fun y:Vectors P G=> _) ?_; intro y
 -- need chip 0=0 even h branches; include h
 have hc:= (smooth_chip P K hb t (canon P)).2
 refine le_trans hc.le ?_
 unfold chip costume temperatures; obtain a|(_|a) := t
 · exact (G.price_range _).1
 · exact le_rfl
 exact mul_nonneg K.penalty_pos.le (G.price_range _).1

lemma tooth_cost (hb:P.Branches K G)(t:Mold)(w:Vectors P G)(d:ℕ):∃ B:ℝ, 0≤B∧ ∀ (v:Vectors P G)(τ:ℝ),0<τ→ ‖τ • v‖ ≤2*Q.width→
     |τ⁻¹*fderiv ℝ (chip P K t (canon P)) (τ • v) w -∑ n∈Finset.range (d+1),τ^n *tooth (K:=K) P t w (n+1) v|≤B*τ^(d+1)*‖v‖^(d+2):=by
 let f(y:Vectors P G):=fderiv ℝ (chip P K t (canon P)) y w
 have he(x)(ht:x∈closedBall (0:Vectors P G) (2*Q.width)):ContDiffAt ℝ ∞ f x:=by
   apply ContDiffAt.clm_apply _ contDiffAt_const
   rw [mem_closedBall_zero_iff] at ht
   exact ((Q.analytic t x (ht.trans (by linarith [Q.active]))).fderiv_right (m:=ω) (by simp)).of_le le_top
 obtain ⟨B,hB,H⟩:=radial_collar (by have :=Q.active; positivity) he (d+1)
 refine ⟨B,hB,fun v τ hv hx=>?_⟩
 have hE:=H v τ hv hx
 change |τ⁻¹ * f (τ • v)- _| ≤ _
 rw [show τ⁻¹*f (τ • v)-∑ n∈Finset.range (d+1),τ^n * tooth P t w (n+1) v= τ⁻¹*(f (τ • v)-∑ n∈Finset.range (d+2),τ^n*jet f n v) from ?_,abs_mul,abs_of_pos (inv_pos.mpr hv)]
 · apply (mul_le_mul_of_nonneg_left hE (by positivity)).trans_eq
   change τ⁻¹ * (B * τ^(d+1+1) * ‖v‖^(d+2)) = _; rw [pow_succ τ (d+1)]; field_simp
 rw [mul_sub,Finset.sum_range_succ' (fun n=>τ^n*jet f n v) (d+1),show jet f 0 v=0 from congr_fun (first_w hb t w) v,mul_zero,add_zero,Finset.mul_sum]; apply congr_arg; refine Finset.sum_congr rfl fun n _=>?_ ; rw [pow_succ]; field_simp; rfl
lemma gum_cost (hA:LocalRatio A)(w:G.Color)(d:ℕ):∃ B:ℝ,0≤B∧∀(v:G.Color)(τ:ℝ), 0<τ→ ‖τ • v‖ ≤ 2*Q.width →
   |τ * Cuff.haarScore (A:=A) (τ • v) w - ∑ n∈Finset.range d,τ^(n+1)*gum A w n v| ≤ B*τ^(d+1)*‖v‖^d:=by
 let f(x:G.Color):=Cuff.haarScore (A:=A) x w
 let Z:=closedBall (0:G.Color) (2*Q.width)
 have he(x)(hx:x∈Z): ContDiffAt ℝ ∞ f x:=by
   have h:ContDiffAt ℝ ω A.J x:= hA.germ _ ((Q.withinH) hx)
   exact ((((h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const).div h
     (hA.pos _ (Q.withinH hx)).ne').of_le le_top)
 cases d with
 | zero=>
   obtain ⟨B,H⟩:= (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (show ContinuousOn f Z from fun x hx=>(he x hx).continuousAt.continuousWithinAt)
   refine ⟨|B|,abs_nonneg _,fun v t ht hz=>?_⟩
   simp only [Finset.range_zero, Finset.sum_empty, sub_zero, abs_mul,abs_of_nonneg ht.le,zero_add,pow_one,pow_zero,mul_one,mul_comm t]
   exact mul_le_mul_of_nonneg_right ((H (t • v) (mem_closedBall_zero_iff.mpr hz)).trans (le_abs_self _)) ht.le
 | succ n=>
   obtain ⟨B,hB,H⟩:=radial_collar (by have :=Q.active; positivity) he n
   refine ⟨B,hB,fun v τ ht hx=>?_⟩
   have h:=H v τ ht hx
   calc
     _ = τ*|f (τ • v)-∑ i∈Finset.range (n+1),τ^i*jet f i v| := by
        rw [←abs_of_pos ht,←abs_mul, abs_of_pos ht, mul_sub,Finset.mul_sum]; simp only [pow_succ,mul_right_comm _ τ,gum,f,mul_comm τ]
     _ ≤ τ*(B*τ^(n+1)*‖v‖^(n+1)):=by gcongr
     _ = _:=by rw [pow_succ τ (n+1)]; ring
end YM.AveragedStep
