import YM.RG12.Arche.Shapes
/-!
# Free coercive measurements on generic RH layouts
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset Lattice RG Source Analysis Ward
open scoped Topology BigOperators RealInnerProductSpace Classical
variable {G:Gauge} (H : Labels.Frames G) (d e:ℕ)
open Extra.FD Shapes Maxwell
local notation "Y!"=> freeTable H
set_option quotPrecheck false
local notation:max "V!" d:max=> (Y!).Field d

-- scale-variable leading and *independent* test.
def polished (a:Axis)(t s:ℝ) (x:V! d)(y:V! e):ℂ:= paired (Y!) d e (compass a t s) x ((Y!).adj (table_spin H) e a y)

set_option maxHeartbeats 260000 in
theorem face_price (a:Axis)(s:ℝ)(hs:0<s)(x y:V! d):
    polished H d d a 0 s x y=duplex (s • basis a) (-(s • basis a)) (writes H d x) (writes H d y):=by
    unfold polished; rw [flat,pair_at]; unfold disc; rw [← scan_used, ← faceTest_eq H d]
    apply congr_arg (readsTwo H d _ _ x)
    unfold faceTest; rw [facing _ _ hs.ne']; apply writes_inj H d
    rw [ride_at,writes_bar]
    obtain ⟨q,hq⟩:= (Y!).onto _ y
    -- tell types, avoid rewriting by rfl too much
    rw [← hq,Table.adj_project,writes_project,writes_project]
    exact (polish_act H (star q) (Signed.reflect a)).trans (congr_arg _ (polish_conj H q))

-- parity even not required. NOTE ComplexOrder statement is strictly on independent vectors!
open scoped ComplexOrder in
lemma central (a:Axis)(s:ℝ)(hs:0<s)(x:V! d)(hx:x≠0): 0 < (polished H d d a 0 s x x).re :=by
   let z:= s • basis a; have he : basis a ≠ (0:E4):= fun hh=>by have := congr_arg (fun v:E4=>v a) hh; change basis a a = (0:ℝ) at this; simp at this
   have hZ : z≠ -z:=by
      intro hz; have hh:=congr_arg (fun v:E4=>v a) hz; change s*basis a a= -(s*basis a a) at hh; rw [show basis a a=1 from by simp] at hh; linarith
   have hy:= (@reflected_positive G z (-z) hZ (writes H d x)).mpr (fun he=>hx ((writes_inj H d) (he.trans (map_zero _).symm)))
   rw [face_price H d a s hs]
   -- ComplexOrder: PosDef? use Complex.lt_def
   exact hy.1

-- continuous in BOTH field slots via exact basis expansion (all disciplines use *fixed*
-- lead forms). Includes scale variable for grid overshoot.
lemma spoke (a:Axis){t s:ℝ}(_hs:0<s): ContinuousAt (fun r:ℝ×ℝ=>compass a r.1 r.2) (t,s):=by
   apply Continuous.continuousAt
   haveI : IsBoundedSMul ℝ (Points 2):= .of_norm_smul_le NormedSpace.norm_smul_le
   have hf:Continuous (bearing a):= by
     unfold bearing; change Continuous fun t=> WithLp.toLp 2 (![_, Ortho.motion (Signed.reflect a) (1 • other a t)]: Fin 2→E4)
     apply (PiLp.continuous_toLp 2 _).comp; apply continuous_pi; intro i; fin_cases i
     · exact continuous_const
     simp_rw [one_smul]; exact (Ortho.motion (Signed.reflect a)).continuous.comp (continuous_other a)
   simp_rw [Shapes.scaling a]; exact continuous_snd.smul (hf.comp continuous_fst)
private def white (a:Axis)(q:ℝ×ℝ): V! d→ₗ[ℝ](V! e→ₗ[ℝ] ℂ):=
    let c:V! e→ₗ[ℝ] V! e:= {
      toFun:=(Y!).adj (table_spin H) e a
      map_add':=map_add _
      map_smul':=fun t v=>by
        change _ = t • _
        rw [show t • v=(t:ℂ) • v from RCLike.real_smul_eq_coe_smul .., map_smulₛₗ,Complex.conj_ofReal,RCLike.real_smul_eq_coe_smul (K:=ℂ) t]; rfl }
    let Z:=paired (Y!) d e (compass a q.1 q.2)
    { toFun:=fun x=> ((Z x).restrictScalars ℝ).comp c
      map_add':=fun x y=>LinearMap.ext (fun t=>by simp)
      map_smul':=fun t x=>LinearMap.ext (fun y=>by
        change Z (t • x) (c y)= t • Z x (c y);
        rw [show Z (t • x)=t • Z x from (Z.restrictScalars ℝ).map_smul t x,LinearMap.smul_apply]) }
private lemma par {L:Register G}(Z:Table L) (hz:Z.Smooth) (x:Z.Field d) (y:Z.Field e) {u:Points 2}(hj:u∈conf _): ContinuousAt (fun t=> paired Z d e t x y) u:=by
  let v:= ![(⟨d,x⟩:Z.Tag),⟨e,y⟩]
  simp_rw [pair_at]
  exact (Next.UVStress.smoothDisc hz v).continuousOn.continuousAt ((conf_open _).mem_nhds hj)

lemma clear_cost (a:Axis){t s:ℝ}(hs:0<s)(x:V! d)(y:V! e):
    ContinuousAt (fun r:(ℝ×ℝ)× (V! d× V! e)=>polished H d e a r.1.1 r.1.2 r.2.1 r.2.2) ((t,s),(x,y)):=by
   let p:= polished H d e a; let q := ((t,s),(x,y))
   have he(i : V! d)(j : V! e):ContinuousAt (fun z:ℝ×ℝ=>p z.1 z.2 i j) (t,s):=by
      let x:= (Y!).adj (table_spin H) _ a j
      have ht:= par d e (Y!) (table_smooth _) i x (opens a t s hs)
      exact ContinuousAt.comp_of_eq (f:=fun r:ℝ×ℝ=> compass a r.1 r.2) ht (spoke a hs) (y:=compass a t s) rfl
   let B₁:= Module.finBasis ℝ (V! d); let B₂:=Module.finBasis ℝ (V! e)
   have hv {t s : ℝ} (x:V! d)(y:V! e) : p t s x y=∑ i,∑ j,(B₁.coord i x * B₂.coord j y) • p t s (B₁ i) (B₂ j):=by
      let g:=white H d e a (t,s)
      change g x y=∑ i,∑ j,(B₁.coord i x * B₂.coord j y) • g (B₁ i) (B₂ j)
      conv_lhs => rw [← B₁.sum_repr x,← B₂.sum_repr y,map_sum g,LinearMap.sum_apply]
      apply Finset.sum_congr rfl; intro i _; rw [map_smul,LinearMap.smul_apply,map_sum,Finset.smul_sum]; refine Finset.sum_congr rfl (fun j _=> ?_); rw [map_smul,smul_smul]; rfl
   change ContinuousAt (fun r:(ℝ×ℝ)×(V! d× V! e)=> p _ _ _ _) q
   rw [show (fun r:(ℝ×ℝ)× (V! d× V! e)=> p r.1.1 r.1.2 r.2.1 r.2.2) = (fun r=>∑ i,∑ j,(B₁.coord i r.2.1*B₂.coord j r.2.2) • p r.1.1 r.1.2 (B₁ i) (B₂ j)) from funext fun r=> hv ..]
   exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> (((B₁.coord i).continuous_of_finiteDimensional.comp (continuous_fst.comp continuous_snd)).mul ((B₂.coord j).continuous_of_finiteDimensional.comp (continuous_snd.comp continuous_snd)) |>.continuousAt.smul (ContinuousAt.comp_of_eq (f:=fun r:(ℝ×ℝ)× (V! d× V! e)=>r.1) (g:=fun r:ℝ×ℝ=>p r.1 r.2 _ _) (he _ _) continuousAt_fst rfl))))



-- Core leading control. Compact parameter interval [1,2*l] for any fixed request,
-- same generic RH test. 
def protect (d:ℕ)(P:ℝ) := Icc 1 P ×ˢ Metric.sphere (0:V! d) 1
lemma close_shapes (a:Axis) {P:ℝ}(_hP:1≤P): ∃ c K:ℝ,0<c∧1 ≤ K ∧ ∀ᶠ t in 𝓝 (0:ℝ), ∀ i:ℝ× V! d, i ∈ protect H d P →
    let b:=(polished H d d a t i.1 i.2 i.2).re
    c ≤ b ∧ b ≤ K:=by
   let R:= protect H d P; let v(u:ℝ× (ℝ × V! d)) := (polished H d d a u.1 u.2.1 u.2.2 u.2.2).re
   have hc : IsCompact R:= isCompact_Icc.prod (isCompact_sphere ..)
   let B:= Set.Icc (-1:ℝ) 1 ×ˢ R
   have hB : IsCompact B:= isCompact_Icc.prod hc
   have hg(r:ℝ× ℝ × V! d)(h : 0<r.2.1):ContinuousAt v r:=by
      have hx: Continuous (fun s:ℝ × (ℝ × V! d)=> ((s.1,s.2.1),s.2.2,s.2.2)):=by fun_prop
      have hh:=clear_cost H d d a (t:=r.1) h r.2.2 r.2.2
      exact Complex.continuous_re.continuousAt.comp (ContinuousAt.comp_of_eq (f:=fun s:ℝ× (ℝ × V! d)=>((s.1,s.2.1),s.2.2,s.2.2)) hh hx.continuousAt rfl)
   have ht (i:ℝ × V! d)(hp:i∈R):0 < i.1:= zero_lt_one.trans_le hp.1.1
   have hp:ContinuousOn (fun i=>v (0,i)) R:=fun i hi=>
     ((hg (0,i) (ht _ hi)).comp (f:=fun j => ((0:ℝ), j)) (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
   by_cases hu : R.Nonempty
   · obtain ⟨i,hi,hU⟩:= hc.exists_isMinOn hu hp
     have hx:‖i.2‖=1 := by simpa using (show _ from hi.2 : i.2∈ Metric.sphere 0 1)
     have hI:0<v (0,i):= central H d a _ (ht _ hi) _ (norm_ne_zero_iff.mp (hx ▸ one_ne_zero))
     have hf:ContinuousOn v B:= fun i h=> (hg i (ht _ h.2)).continuousWithinAt
     obtain ⟨K,hK⟩:= (hB.image_of_continuousOn hf).bddAbove
     obtain ⟨δ,hδ,hq⟩:= Metric.uniformContinuousOn_iff.mp (hB.uniformContinuousOn_of_continuous hf) (v (0,i)/2) (half_pos hI)
     refine ⟨v (0,i)/2,max K 1,half_pos hI,le_max_right ..,?_⟩
     filter_upwards [Metric.ball_mem_nhds _ hδ, Icc_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with u hr hp i' hi'
     intro b
     have hp':(u,i')∈ B:=⟨hp,hi'⟩
     have h:= abs_le.mp (lt_iff_le_and_ne.mp (show |v (0,i') - v (u,i')| < v (0,i)/2 from hq _ (show ((0:ℝ),i')∈B from ⟨by norm_num,hi'⟩) _ hp' (by rw [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)]; rw [dist_comm]; exact hr)) |>.1)
     refine ⟨?_, (hK (mem_image_of_mem _ hp')).trans (le_max_left ..)⟩
     change _ ≤ v (u,i'); linarith [show v (0,i) ≤ v (0,i') from hU hi']
   exact ⟨1,1,zero_lt_one,le_rfl, Eventually.of_forall fun _ i h=> False.elim (hu ⟨i,h⟩)⟩

lemma worthwhile (a:Axis){P:ℝ}(hP:1≤P): ∃ c K:ℝ,0<c∧1≤K∧∀ᶠ n:ℕ in atTop, ∀ s∈Set.Icc 1 P, ∀ v : V! d,
   let b:=(polished H d d a (n:ℝ)⁻¹ s v v).re
   c*‖v‖^2≤b ∧ b≤K*‖v‖^2:=by
  obtain ⟨c,K,hc,hK,h⟩:= close_shapes H d a hP
  have ht:Tendsto (fun n:ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨_,_,hc,hK,?_⟩
  filter_upwards [ht.eventually h] with n hn s hs v b
  let p:=white H d d a ((n:ℝ)⁻¹,s)
  change _ ≤ (p v v).re ∧ _
  change _ ≤ _ ∧ (p v v).re ≤ _
  rcases eq_or_lt_of_le (norm_nonneg v) with hx|hx
  · have hv:= norm_eq_zero.mp hx.symm; subst v; simp
  let x:= ‖v‖⁻¹ • v; have hh:‖x‖=1:=by unfold x; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hx.le), inv_mul_cancel₀ hx.ne']
  have he : v = ‖v‖ • x:= by unfold x; rw [smul_smul,mul_inv_cancel₀ hx.ne',one_smul]
  obtain ⟨h₁,h₂⟩:= (show c ≤ (p x x).re∧ (p x x).re ≤ K from hn (s,x) ⟨hs,by simpa using hh⟩)
  rw [show (p v v).re = ‖v‖^2*(p x x).re from ?_]; constructor <;> nlinarith [h₁,h₂,sq_nonneg ‖v‖,mul_le_mul_of_nonneg_left h₁ (sq_nonneg ‖v‖),mul_le_mul_of_nonneg_left h₂ (sq_nonneg ‖v‖)]
  conv_lhs => rw [he,map_smul p,LinearMap.smul_apply,map_smul,smul_smul]
  simp [sq]

end YM.RG12.Arche
