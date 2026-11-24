import YM.SchemeConversionRG11.Maxwell.Connected

/-! # Trivial identity neighborhood and finite quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open scoped Topology BigOperators RealInnerProductSpace InnerProduct
variable {G : Gauge}

lemma lingering (H : G.Simple) (T : ℕ → Door G) (h : Tendsto T atTop (𝓝 1)) (hx : ∀ i,T i≠1)
    (ht : ∀ i,T i∈ Tracks G) (hy : ∀ i, Closer (T i)) : False := by
  classical
  let s := fun i ↦ ‖T i-1‖
  have hs (i) : 0<s i := norm_pos_iff.mpr (sub_ne_zero.mpr (hx i))
  have hm : Tendsto s atTop (𝓝 0) := by
    have hl : Tendsto (fun i ↦ T i - 1) atTop (𝓝 0) := by simpa using h.sub_const 1
    simpa [s] using hl.norm
  let D i := (s i)⁻¹ • (T i-1)
  have he (i) : ‖D i‖=1 := by
    unfold D; rw [norm_smul,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hs i)), inv_mul_cancel₀ (hs i).ne']
  obtain ⟨w,_,n,hn,hw⟩ := (isCompact_closedBall (0:Door G) 1).isSeqCompact (fun i ↦ show D i∈closedBall 0 1 by rw [mem_closedBall, dist_zero_right,he])
  have hq : Tendsto (s ∘ n) atTop (𝓝 0) := hm.comp hn.tendsto_atTop
  have hW : w∈Store G := toward_one H (T ∘ n) (D ∘ n) (s ∘ n) hq (fun i ↦ (hs _).ne') (fun _ ↦ ht _) (fun i ↦ by
    simp only [Function.comp_apply,D]; rw [smul_inv_smul₀ (hs _).ne']; abel) hw
  obtain ⟨x,hv⟩ := hW
  let U (t:ℝ) := G.lieExp (t • x) -- annotate
  have hk : HasDerivAt (fun t:ℝ ↦ firm (G:=G) (U t)) w 0 := hv ▸ firm_flow x
  have hh : Tendsto (s ∘ n) atTop (𝓝[≠] 0) := tendsto_nhdsWithin_iff.mpr ⟨hq, Eventually.of_forall fun i ↦ (hs (n i)).ne'⟩
  let V i := (s (n i))⁻¹ • (firm (U (s (n i)))-1)
  have hP : Tendsto V atTop (𝓝 w) := by
    have hz : U 0=1 := by simp [U]
    have hu := hk.tendsto_slope.comp hh
    simp only [slope_def_module, sub_zero, Function.comp_def] at hu
    change Tendsto (fun j:ℕ ↦ (s (n j))⁻¹ • (firm (U (s (n j)))-firm (U 0))) _ _ at hu
    rw [hz,firm_one] at hu; exact hu
  let r := fun i ↦ ‖D (n i)-V i‖
  have hr : Tendsto r atTop (𝓝 0) := by simpa only [r, Function.comp_def, sub_self,norm_zero] using (hw.sub hP).norm
  obtain ⟨i,hi⟩ := (hr.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))).exists
  refine not_le.mpr hi ?_
  let j:= n i
  calc
    (1:ℝ) = (s j)⁻¹ * ‖T j-1‖ := Eq.symm (inv_mul_cancel₀ (hs _).ne')
    _ ≤ (s j)⁻¹ * ‖T j-firm (U (s j))‖ := mul_le_mul_of_nonneg_left (hy _ _) (inv_pos.mpr (hs _)).le
    _ = r i := by unfold r V D j; rw [← smul_sub (s (n i))⁻¹ (T (n i)-1),sub_sub_sub_cancel_right,norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hs _))]

lemma accessible (H : G.Simple) : ∀ᶠ R : Door G in 𝓝 1, R∈Tracks G → ∃ u : G.El,R=firm u := by
  classical
  by_contra hn
  have hv : (1:Door G)∈closure (Tracks G \ Set.range (fun u : G.El ↦ firm u)) := by
    refine mem_closure_iff_frequently.mpr (Filter.Frequently.mono (not_eventually.mp hn) (fun x hx ↦ ?_))
    simp only [Classical.not_imp] at hx; exact ⟨hx.1, fun ⟨i,hi⟩ ↦ hx.2 ⟨i,hi.symm⟩⟩
  obtain ⟨T,hT,Ht⟩ := mem_closure_iff_seq_limit.mp hv
  choose L hL hr hi hm using fun i : ℕ ↦ around (show T i∈Tracks G from (hT i).1) (fun u he ↦ (hT i).2 ⟨u,he⟩)
  apply lingering H L _ hi hL hr
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ ↦ norm_nonneg _) hm (tendsto_iff_norm_sub_tendsto_zero.mp Ht)

lemma cosets (H : G.Simple) : ∃ S : Finset (Door G), ∀ x∈Tracks G,∃ v∈S, ∃ u : G.El, x=firm u*v := by
  classical
  let F (v : Door G) := {x : Door G|x∈Tracks G → ∃ u : G.El,x=firm u*v}
  have hF (x : Door G) (hx : x∈Tracks G) : F x ∈ 𝓝 x := by
    have h : Fair x := hx.1
    have he : Tendsto (fun R : Door G ↦ R*x†) (𝓝 x) (𝓝 1) := by rw [← h.inv']; exact (continuous_id.mul continuous_const).continuousAt
    show ∀ᶠ y in 𝓝 x,y∈Tracks G→ ∃ u : G.El, y=firm u*x
    filter_upwards [he.eventually (accessible H)] with y hy
    intro hh; obtain ⟨u,hu⟩ := hy (inMul hh (inInv hx)); exact ⟨u,by rw [← hu,mul_assoc,h.inv,mul_one]⟩
  obtain ⟨s,_,hs⟩ := (pier G).elim_nhds_subcover F hF
  refine ⟨s,fun x hx ↦ ?_⟩; obtain ⟨v,he⟩ := Set.mem_iUnion.mp (hs hx); obtain ⟨j,hv⟩ := Set.mem_iUnion.mp he; exact ⟨v,j,hv hx⟩
lemma invariant_firm {d : ℕ} (p : WickPol G) (h : p∈shellSector G d) (u : G.El) (A : TaylorTower G) : Maxwell.probe (commerce (firm u) A) p=Maxwell.probe A p := (pigment_action u A p).symm.trans (congr_arg _ ((sector.mp h).2 _))

theorem finitely (H : G.Simple) {d : ℕ} (p : WickPol G) (h : p∈shellSector G d) (A : TaylorTower G) :
    Set.Finite ((fun R : Door G ↦ Maxwell.probe (commerce R A) p) '' Tracks G) := by
  obtain ⟨s,hs⟩ := cosets H; let f (R : Door G) := Maxwell.probe (commerce R A) p
  refine ((s.finite_toSet).image f).subset ?_
  rintro i ⟨u,hu,rfl⟩; obtain ⟨v,hv,r,hx⟩ := hs _ hu
  refine ⟨v,hv,?_⟩
  change f v= f u; rw [hx]
  change _=Maxwell.probe (commerce (firm r ∘L v) A) p; rw [commerce_comp,invariant_firm p h]
end YM.SchemeConversionRG11.Corona
