import YM.UVExt.PathSlice
import YM.Analysis.SmoothJets
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Real Wilson Function Filter Set Tensor OrderedFinpartition
open scoped ContDiff BigOperators Topology Classical
variable {α : Type*} {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma view_cont {k : ℕ} : Continuous (fun p : T E F k × (Fin k→E) => p.1 p.2) := (ContinuousLinearMap.id ℝ (T E F k)).continuous_uncurry_of_multilinear
variable {q : ℕ}
abbrev fish (j:ℕ) (f:ℝ→F) := iteratedDeriv j f 0
lemma finite_cap (i : ℕ) : (i:ℕ∞ω) ≤ ∞ := by rw [← WithTop.coe_natCast (α:=ENat)]; exact WithTop.coe_le_coe.mpr le_top

lemma ray_tag (f : E→F) (h : ContDiffAt ℝ q f 0) u : fish q (fun t : ℝ=> f (t • u)) = Tensor.diagonal (iteratedFDeriv ℝ q f 0) u := by
  unfold fish; let a := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  change iteratedDeriv q (f ∘ (⇑a)) 0=_
  rw [iteratedDeriv_eq_iteratedFDeriv, Next.Foundations.jets_linear _ h]; exact congr_arg (iteratedFDeriv ℝ q f 0) (funext (fun i=> by unfold a; change (1:ℝ) • u=u; rw [one_smul]))

variable [FiniteDimensional ℝ F] [CompleteSpace F]
lemma unique_tensor {γ : ℕ→T E F q} (hg : ∀ i, Sym (γ i)) (h : ∃ a:E→F,∀ u, Tendsto (fun i=> Tensor.diagonal (γ i) u) atTop (𝓝 (a u))) [FiniteDimensional ℝ E] :
    ∃ G' : T E F q, Tendsto γ atTop (𝓝 G') := by
  apply cauchySeq_tendsto_of_complete
  obtain ⟨g,h⟩ := h
  rw [Metric.cauchySeq_iff]; by_contra! hw
  obtain ⟨ε,he,H⟩ := hw; choose m hm n hn hz using H
  have hm' : Tendsto m atTop atTop := tendsto_atTop_mono hm tendsto_id
  have hn' : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  let X i := γ (m i) - γ (n i)
  let Z i := (‖X i‖⁻¹:ℝ) • X i
  have hX i : ε ≤ ‖X i‖ := by simpa only [X,dist_eq_norm] using hz i
  have hZ i : ‖Z i‖ = 1 := by simp [Z,norm_smul,inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le he (hX i)))]
  obtain ⟨A,-,k,hk,hj⟩ := (ProperSpace.isCompact_closedBall (0:T E F q) 1).tendsto_subseq (fun i=>by simpa only [Metric.mem_closedBall,dist_zero_right] using (hZ i).le)
  have hA : ‖A‖=1 := tendsto_nhds_unique hj.norm (tendsto_const_nhds.congr (fun i : ℕ=> (hZ (k i)).symm))
  have hel (u : E) : Tendsto (fun i=> Tensor.diagonal (X i) u) atTop (𝓝 0) := by simpa only [X,Tensor.diagonal,Function.comp_apply,sub_apply,sub_self] using ((h u).comp hm').sub ((h u).comp hn') -- remove Tsymm
  have hb (u : E) : Tendsto (fun i=>Tensor.diagonal (Z i) u) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) (Eventually.of_forall ?_) (show Tendsto (fun i=> ε⁻¹ * ‖Tensor.diagonal (X i) u‖) atTop (𝓝 0) by simpa only [norm_zero,mul_zero] using ((hel u).norm.const_mul (ε⁻¹))))
    intro i
    change ‖((‖X i‖)⁻¹:ℝ) • (Tensor.diagonal (X i) u)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right ((inv_le_inv₀ (lt_of_lt_of_le he (hX i)) he).mpr (hX i)) (norm_nonneg _)
  have hsym i : Sym (Z i) := fun t j => by unfold Z X; simp only [smul_apply, sub_apply,hg (n i) t j, hg (m i) t j]
  have ht (s) := ((view_cont (k:=q) (F:=F) (E:=E)).tendsto (A,s)).comp (hj.prodMk_nhds tendsto_const_nhds)
  have hB : Sym A := fun t j => tendsto_nhds_unique ((ht (t∘j))) ((ht t).congr (fun i : ℕ => (hsym (k i) t j).symm))
  have hy (u : E) : Tensor.diagonal A u=0 := tendsto_nhds_unique (ht (fun _=>u)) ((hb u).comp hk.tendsto_atTop)
  have hAA := ext_diag A 0 hB (fun _ _=>by simp) (funext fun u=> (hy u).trans (by rw [Tensor.diagonal]; rfl))
  rw [hAA,norm_zero] at hA; exact zero_ne_one hA

variable [FiniteDimensional ℝ E] [CompleteSpace E]
abbrev spray (f : ℕ→E→F) (k : ℕ) := fun i=> iteratedFDeriv ℝ k (f i) 0
lemma tensor_lim {f : ℕ→E→F} (ha : ∀ᶠ i : ℕ in atTop, ContDiffAt ℝ q (f i) 0) (X : E→F) (hX : ∀ u, Tendsto (fun i=> fish q (fun t : ℝ=>f i (t • u))) atTop (𝓝 (X u))) : ∃ A:T E F q, Tendsto (spray f q) atTop (𝓝 A) ∧ Tensor.diagonal A=X := by
  let g i := if _h:ContDiffAt ℝ q (f i) 0 then spray f q i else 0
  have he : g =ᶠ[atTop] spray f q := ha.mono fun i hi=> dif_pos hi
  have hg (u : E) : Tendsto (fun i=>Tensor.diagonal (g i) u) atTop (𝓝 (X u)) := (hX u).congr' (ha.mono fun i hi=>by rw [ray_tag _ hi]; exact Eq.symm <| (show _ from congr_arg (Tensor.diagonal · u) (dif_pos hi : g i= spray f q i)))
  obtain ⟨A,hA⟩ := unique_tensor (γ:=g) (by
      intro i; unfold g; split
      · exact Analysis.sym_Jet (by assumption)
      intro t j; simp) ⟨X,hg⟩
  refine ⟨A,hA.congr' he, funext fun x=> tendsto_nhds_unique (((view_cont (E:=E)).continuousAt).tendsto.comp <| hA.prodMk_nhds (tendsto_const_nhds (x:=fun _=>x))) (hg x)⟩

variable {f g : ℕ→E→F} {k : ℕ}

def Junction (f g : ℕ→E→F) (n : ℕ) : Prop := ∀ q≤n, ∃ A : T E F q, Tendsto (spray f q) atTop (𝓝 A) ∧ Tendsto (spray g q) atTop (𝓝 A)

def lucid (f : ℕ→E→F) := ∀ᶠ i : ℕ in atTop, ContDiffAt ℝ ∞ (f i) 0
lemma Junction.mono {m : ℕ} (h : Junction f g k) (hh : m≤k) : Junction f g m := fun q hq => h q (hq.trans hh)
lemma Junction.evaluate (h : Junction f g k) {ρ : ℕ} (hr : ρ≤k) (P P' : ℕ→Fin ρ→E) {W : Fin ρ→E} (hp : ∀ i, Tendsto (fun x=>P x i) atTop (𝓝 (W i))) (hP : ∀ i, Tendsto (fun x=> P' x i) atTop (𝓝 (W i))) :
    ∃ u, Tendsto (fun x=> spray f ρ x (P x)) atTop (𝓝 u) ∧ Tendsto (fun x=> spray g ρ x (P' x)) atTop (𝓝 u) := by
  obtain ⟨A,h₁,h₂⟩ := h _ hr
  exact ⟨A W,view_cont.continuousAt.tendsto.comp (h₁.prodMk_nhds (tendsto_pi_nhds.mpr hp)),view_cont.continuousAt.tendsto.comp (h₂.prodMk_nhds (tendsto_pi_nhds.mpr hP))⟩
lemma junction_line (h : Junction f g k) (hc : lucid f) (hd : lucid g) {m : ℕ} (hm : m≤k) (v : E) :
    ∃ t, Tendsto (fun x=>fish m (fun t : ℝ=> f x (t • v))) atTop (𝓝 t) ∧ Tendsto (fun x=>fish m (fun t : ℝ=> g x (t • v))) atTop (𝓝 t) := by
  obtain ⟨s,h₁,h₂⟩ := h.evaluate hm (fun _ _=>v) (fun _ _=>v) (fun _=>tendsto_const_nhds) (fun _=>tendsto_const_nhds)
  exact ⟨s,h₁.congr' (hc.mono fun x hx=>(ray_tag (f x) ((show ContDiffAt ℝ ∞ _ _ from hx).of_le (m:=m) (finite_cap _)) v).symm), h₂.congr' (hd.mono fun x hx=>(ray_tag (g x) ((show ContDiffAt ℝ ∞ _ _ from hx).of_le (m:=m) (finite_cap _)) v).symm)⟩
lemma junction_self {f : E→F} : Junction (fun _=>f) (fun _=> f) k := fun _ _ => ⟨_,tendsto_const_nhds, tendsto_const_nhds⟩
lemma Junction.zero_args (h : Junction f g k) (h₁ : lucid f) (h₂ : lucid g) : ∃ z, Tendsto (fun i=> f i 0) atTop (𝓝 z) ∧ Tendsto (fun i=>g i 0) atTop (𝓝 z) := by
    simpa only [iteratedDeriv_zero,fish,zero_smul] using junction_line h h₁ h₂ (Nat.zero_le k) (0:E)
lemma viaDiag (ha : lucid f) (hb : lucid g) (h : ∀ m≤k,∀ v : E, ∃ j, Tendsto (fun x=>fish m (fun t : ℝ=> f x (t • v))) atTop (𝓝 j) ∧ Tendsto (fun x=>fish m (fun t : ℝ=> g x (t • v))) atTop (𝓝 j)) : Junction f g k := by
  intro m hm; choose A h1 h2 using h m hm
  obtain ⟨X,hX,eX⟩ := tensor_lim (f:=f) (ha.mono fun _ hx=>(show ContDiffAt ℝ ∞ _ _ from hx).of_le (m:=m) (finite_cap _)) _ h1
  obtain ⟨Y,hY,eY⟩ := tensor_lim (f:=g) (hb.mono fun _ hx=>(show ContDiffAt ℝ ∞ _ _ from hx).of_le (m:=m) (finite_cap _)) _ h2
  have hXY : X=Y := ext_diag X Y ?_ ?_ (eX.trans eY.symm)
  · exact ⟨X,hX,hXY ▸ hY⟩
  · intro v t
    apply tendsto_nhds_unique (((view_cont (E:=E) (F:=F) (k:=m)).tendsto (X,v∘t)).comp (hX.prodMk_nhds tendsto_const_nhds))
    exact (((view_cont (E:=E) (F:=F) (k:=m)).tendsto (X,v)).comp (hX.prodMk_nhds tendsto_const_nhds)).congr' (ha.mono fun i hi=> (Analysis.sym_Jet ((show ContDiffAt ℝ ∞ _ _ from hi).of_le (m:=m) (finite_cap _)) _ _).symm)
  intro v t
  apply tendsto_nhds_unique (((view_cont (E:=E) (F:=F) (k:=m)).tendsto (Y,v∘t)).comp (hY.prodMk_nhds tendsto_const_nhds))
  exact (((view_cont (E:=E) (F:=F) (k:=m)).tendsto (Y,v)).comp (hY.prodMk_nhds tendsto_const_nhds)).congr' (hb.mono fun i hi=> (Analysis.sym_Jet ((show ContDiffAt ℝ ∞ _ _ from hi).of_le (m:=m) (finite_cap _)) _ _).symm)
end YM.UVExt.Paths
