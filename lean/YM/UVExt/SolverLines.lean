import YM.UVExt.PrunedJets

/-! No implicit equation existence claim. Fixed directional equations on the real critical germ; the higher path coefficients not just the first tangent have to obey them. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Set Real Matrix
open scoped Topology ContDiff BigOperators Classical
variable {B F E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup E] [NormedSpace ℝ E]

def paired (x : F) (ρ : ℝ→B) : ℝ→F×B := fun t=> (t • x,ρ t)
lemma pairSmooth (x : F) {ρ : ℝ→B} {q} (h : ContDiffAt ℝ q ρ 0) : ContDiffAt ℝ q (paired x ρ) 0 := (contDiffAt_id.smul contDiffAt_const).prodMk h
variable (x : F) {ρ : ℝ→B} {p : F×B→ℝ}
structure Optimizes (p : F×B→ℝ) (x : F) (ρ : ℝ→B) : Prop where
   anchor : ρ 0=0
   analytic_pay : ContDiffAt ℝ ω ρ 0
   smooth : ContDiffAt ℝ ω p 0
   answers : ∀ᶠ t : ℝ in 𝓝 0, (fderiv ℝ (fun b : B=>p (t • x,b)) (ρ t))=0

variable {x}
lemma pairAnchored (ρ : ℝ→B) (x : F) (h : ρ 0=0) : paired x ρ 0=0 := by simp [paired,h]
lemma linear_next (U : E →L[ℝ] F) (t : ℝ→E) (h : ContDiffAt ℝ ∞ t 0) (q : ℕ) :
    fish q (U ∘ t) = U (fish q t) := by rw [fish, iteratedDeriv_eq_iteratedFDeriv, U.iteratedFDeriv_comp_left h (finite_cap q)]; rfl

lemma tensor1 (h : ContDiffAt ℝ ∞ ρ 0) (x : F) (i : ℕ) : fish i (paired x ρ)=
    (fish i (fun t:ℝ=> t • x),fish i ρ) := by
  apply Prod.ext
  · let g : (F×B)→L[ℝ] F := ContinuousLinearMap.fst ℝ F B
    exact show g _=fish i (g ∘ _) from (linear_next g (paired x ρ) (pairSmooth _ h) i).symm
  let g := ContinuousLinearMap.snd ℝ F B
  exact show g _=fish i (g ∘ _) from (linear_next g (paired x ρ) (pairSmooth _ h) i).symm

lemma tensor_word (n : ℕ) (h : ContDiffAt ℝ ω ρ 0) (x : F) : (fish n (paired x ρ)).1 = if n=1 then x else 0 := by
  rw [tensor1 (h.of_le le_top)]
  let E := (ContinuousLinearMap.id ℝ ℝ).smulRight x
  change fish n (E ∘ (id:ℝ→ℝ))= if n=1 then x else 0
  rw [linear_next E id contDiffAt_id]
  simp only [fish,iteratedDeriv_id]
  split_ifs <;> first |exact map_zero E|exact one_smul ℝ x|omega

lemma partial_eval (x : F) (y : B) (h : DifferentiableAt ℝ p (x,y)) :
    fderiv ℝ (fun v : B=>p (x,v)) y = (fderiv ℝ p (x,y)).comp (ContinuousLinearMap.inr ℝ F B) :=
    (h.hasFDerivAt.comp y ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))).fderiv -- argument const maybe reversed

lemma optimization_stationary (h : Optimizes p x ρ) (v) : Analysis.D (0,v) p ∘ paired x ρ =ᶠ[𝓝 (0:ℝ)] 0 := by
  have hg := (pairSmooth x h.analytic_pay).continuousAt.tendsto
  rw [pairAnchored _ _ h.anchor] at hg
  filter_upwards [h.answers, hg.eventually (h.smooth.eventually (by simp : ω ≠ ∞))] with i hi hl
  exact (show (fderiv ℝ p (i • x, ρ i)) (0,v) = 0 from congr_arg (fun c : B→L[ℝ] ℝ=>c v) ((partial_eval _ _ (hl.differentiableAt (by simp))).symm.trans hi)) -- convert map_zero

lemma snoc_two (a t s : E) : Fin.snoc ![a,t] s = ![a,t,s] := by ext1 i; fin_cases i <;> simp [Fin.snoc]
lemma snoc_one (a s : E) : Fin.snoc ![a] s = ![a,s] := by ext1 i; fin_cases i <;> simp [Fin.snoc]
lemma constant_two (v : E) : (fun _ : Fin 2=>v)=![v,v] := by ext1 i; fin_cases i <;> rfl

lemma SolverRates {ρ : ℝ→B} (h : Optimizes p x ρ) :
   (∀ z:B, fderiv ℝ p 0 (0,z)=0) ∧ ∀ z:B,
     (iteratedFDeriv ℝ 2 p 0 ![(deriv (paired x ρ) 0),(0,z)] = 0) ∧
     iteratedFDeriv ℝ 2 (Analysis.D (0,z) p) 0 ((fun _ : Fin 2=>deriv (paired x ρ) 0)) + iteratedFDeriv ℝ 2 p 0 ![fish 2 (paired x ρ),(0,z)] = 0 := by
  have hG n z := (optimization_stationary h z).iteratedDeriv n |>.eq_of_nhds
  have hh := pairSmooth x h.analytic_pay
  have ha := pairAnchored ρ x h.anchor
  constructor
  · intro z; simpa only [Analysis.D,iteratedDeriv_zero,Function.comp_apply,ha,Pi.zero_apply] using hG 0 z
  intro z
  have ht := Analysis.dSmooth (m:=(∞:ℕ∞ω)) h.smooth (0,z) le_top
  have hs (a b : F×B) : (fderiv ℝ (Analysis.D a p) 0) b = iteratedFDeriv ℝ 2 p 0 ![b,a] := by
     refine Eq.symm ((congr_arg (iteratedFDeriv ℝ (1+1) p 0) (snoc_one b a).symm).trans ((Analysis.snoc_jet (h.smooth.of_le le_top) _ _).trans (iteratedFDeriv_one_apply ![b])))
  constructor
  · specialize hG 1 z
    simp only [iteratedDeriv_one,deriv_const] at hG ⊢; change deriv (Analysis.D _ p ∘ _) _=deriv (fun _ : ℝ=> (0:ℝ)) 0 at hG; rw [deriv_const] at hG
    rw [fderiv_comp_deriv _ ((ha.symm ▸ ht.differentiableAt (by simp))) (hh.differentiableAt (by simp)),ha] at hG
    rwa [hs] at hG
  have hf : fish 2 ((Analysis.D (0,z) p) ∘ paired x ρ)=0 := (hG 2 z).trans (by show iteratedDeriv 2 (fun _ : ℝ=> (0:ℝ)) 0=0; simp [iteratedDeriv_const])
  simpa only [fish,ha,hs] using (Eq.trans ((iteratedDeriv_vcomp_two (ha.symm ▸ ht.of_le (m:=(2:ℕ)) (finite_cap _)) (hh.of_le le_top)).symm) hf)

end YM.UVExt.Paths
