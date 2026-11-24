import YM.SchemeConversionRG11.FirstMS.Triad.String

/-! Off-collision costs and continuation through derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MSbar.Symbol MeasureTheory Metric Complex DR Maxwell Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

def region : Set Patch := {p | 0 < ‖p.1‖^2+p.2}
lemma reg_open : IsOpen region := isOpen_lt continuous_const ((continuous_fst.norm.pow 2).add continuous_snd)

structure Off (F : ℂ → E4 → ℝ → ℂ) : Prop where
   smooth : ∀ z∈neighborhood,∀ p∈region, ContDiffAt ℝ ∞ (fun x:ℂ × Patch => F x.1 x.2.1 x.2.2) (z,p)
   colors : ∀ z∈neighborhood, ∀ p∈region, DifferentiableAt ℂ (fun z=> F z p.1 p.2) z

def axisStep (a:Axis)(F:ℂ→E4→ℝ→ℂ)(z:ℂ)(v:E4)(u:ℝ) := grad a (fun v=> F z v u) v

variable {F G: ℂ → E4 → ℝ → ℂ} (h:Off F)
include h

lemma Off.add (g:Off G) : Off (fun z v u=> F z v u+G z v u) := ⟨fun z hz p hp=> (h.smooth z hz p hp).add (g.smooth z hz p hp),fun z hz p hp=>(h.colors z hz p hp).add (g.colors z hz p hp)⟩
lemma Off.mul (g:Off G): Off (fun z v u=> F z v u*G z v u) := ⟨fun z hz p hp=>(h.smooth z hz p hp).mul (g.smooth z hz p hp),fun z hz p hp=> (h.colors z hz p hp).mul (g.colors z hz p hp)⟩
lemma Off.const (c:ℂ): Off (fun z v u=> c*F z v u):= ⟨fun z hz p hp=> contDiffAt_const.mul (h.smooth z hz p hp), fun z hz p hp=> (h.colors z hz p hp).const_mul _⟩
lemma Off.neg: Off (fun z v u=> - F z v u):= ⟨fun z hz p hp=> (h.smooth z hz p hp).neg,fun z hz p hp => (h.colors z hz p hp).neg⟩
omit h in
lemma Off.join {I:Type*} (s:Finset I) {f:I→ℂ→E4→ℝ→ℂ} (hh:∀ i∈s,Off (f i)): Off (∑ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact ⟨fun z hz p hp=> contDiffAt_const,fun z hz p hp=> differentiableAt_const _⟩
   | insert j s hj ih=> rw [Finset.sum_insert hj]; exact (hh j (Finset.mem_insert_self ..)).add (ih fun i hi=> hh i (Finset.mem_insert_of_mem hi))

lemma Off.deriver (a : Axis): Off (axisStep a F) := by
   let f (q:ℂ × Patch) := F q.1 q.2.1 q.2.2
   have aux (p : Patch)(hp:p∈region) : ∃ g:ℂ × Patch → ℂ, AH neighborhood g ∧ ∀ z∈neighborhood,
      ContDiffAt ℝ ∞ g (z,p) ∧ g =ᶠ[𝓝 (z,p)] fun x=> axisStep a F x.1 x.2.1 x.2.2 := by
      obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp (reg_open.mem_nhds hp)
      let b : ContDiffBump p := ⟨r/4,r/2,by positivity,by linarith⟩
      have hv : tsupport b ⊆ region := by rw [b.tsupport_eq]; exact (closedBall_subset_ball (half_lt_self hr)).trans H
      let d(q:ℂ × Patch):= ↑(b q.2)*f q
      have hd : AH neighborhood d := by
         apply upon_packed opened b.hasCompactSupport (fun z hz x hx=> by simp [d,image_eq_zero_of_notMem_tsupport hx])
         · intro q hq
           by_cases ht:q.2∈tsupport b
           · exact ((ofRealCLM.contDiff.comp (b.contDiff.comp contDiff_snd)).contDiffAt).mul (h.smooth _ hq _ (hv ht))
           apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
           filter_upwards [continuousAt_snd.tendsto.eventually (notMem_tsupport_iff_eventuallyEq.mp ht)] with x hx
           simp only [d,show b x.2=0 from hx,ofReal_zero,zero_mul]
         intro z x hz; by_cases ht:x∈tsupport b
         · exact (h.colors _ hz _ (hv ht)).const_mul  (↑(b x):ℂ)
         have hh(w:ℂ): d (w,x) = 0 := by simp only [d,image_eq_zero_of_notMem_tsupport ht,ofReal_zero,zero_mul]
         simp_rw [hh]; exact differentiableAt_const _
      let g := AH.diff (0,basis a,0) d
      have hg:AH neighborhood g:=hd.diff_smooth opened _
      refine ⟨g,hg,fun z hz=> ⟨hg.smooth _ hz,?_⟩⟩
      have he : d =ᶠ[𝓝 (z,p)] f := ((continuousAt_snd (p:=(z,p))).tendsto.eventually b.eventuallyEq_one).mono (fun y hy=> by simp [d,show b y.2=1 from hy])
      filter_upwards [(opened.prod reg_open).mem_nhds (show (z,p)∈neighborhood ×ˢ region from ⟨hz,hp⟩),eventually_eventually_nhds.mpr he] with q hq he
      unfold g AH.diff axisStep grad D
      change d =ᶠ[𝓝 q] f at he
      rw [he.fderiv_eq]
      let Q(x:E4):ℂ × Patch:= (q.1,x,q.2.2)
      have ht : ∀ x, F q.1 x q.2.2=f (Q x):= fun x=>rfl
      let L := (((ContinuousLinearMap.inr ℝ ℂ Patch).comp (ContinuousLinearMap.inl ℝ E4 ℝ)))
      have hL : HasFDerivAt Q L q.2.1 := by
         convert! ((hasFDerivAt_const (𝕜:=ℝ) q.1 q.2.1).prodMk ((hasFDerivAt_id q.2.1).prodMk (hasFDerivAt_const q.2.2 q.2.1))) using 1
      have hm : DifferentiableAt ℝ f q := (h.smooth _ hq.1 _ hq.2).differentiableAt (by simp)
      rw [funext ht]
      change _ = fderiv ℝ (f ∘ Q) q.2.1 (basis a)
      rw [(hm.hasFDerivAt.comp q.2.1 hL).fderiv]; rfl
   constructor
   · intro z hz p hp
     obtain ⟨g,hg,hH⟩:= aux p hp; exact (hH z hz).1.congr_of_eventuallyEq (hH z hz).2.symm
   intro z hz p hp; obtain ⟨g,hg,hH⟩:= aux p hp; apply (hg.cr z p hz).congr_of_eventuallyEq
   exact (continuousAt_id.prodMk (continuousAt_const (y:=p))).tendsto.eventually (hH z hz).2.symm

omit h
lemma off_bridge : Off bridge := ⟨fun _ hz _ hp=> bridge_ok hz hp,fun _ hz _ hp => bridge_color hz hp⟩
lemma off_lane (b:Bool)(i:Fin 3)(μ: Axis): Off (fun z=> lane z b i μ) :=
    ⟨fun _ hz p hp=> ContDiffAt.sum (fun c _=> ((off_bridge.deriver c).neg.const _).smooth _ hz p hp),
     fun _ hz p hp=> DifferentiableAt.fun_sum (fun c _=> ((off_bridge.deriver c).neg.const _).colors _ hz p hp)⟩
lemma off_bar (b:Bool)(i:Fin 3)(a μ: Axis) : Off (fun z=>bar z b i a μ) := (off_lane b i μ).deriver a
end YM.SchemeConversionRG11.FirstMS.Triad
