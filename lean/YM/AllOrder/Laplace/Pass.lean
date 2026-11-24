import YM.AllOrder.Laplace.Collar
import YM.SectorNext.VACUUM_NORMALIZATION.ForestLine
/-!
# Fan comparability under every germ-preserving slice chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Tested Lattice Function Filter Set Metric Precision Wilson RG Gauge Tree MeasureTheory
open Matrix Finset Push Push.Uniform PhysicalNext Repeat Lapis Fare Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat Next.Fluctuations
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio) (P:ℝ → Config G c)(W:ℝ→Poll.Body (Precision.Key F G)) (H:ℝ→ F.Slice G→ℝ)
local notation "K"=>Precision.Key F G
local notation "Y"=>Poll.Body (Precision.Key F G)
local notation "K[" F' "]"=>Precision.Key F' G
local notation "Y[" F' "]"=>Poll.Body (Precision.Key F' G)
lemma garment (a: F.Free) : Continuous (fun V: Config G c=> Fare.floorG F V a):=by
   unfold floorG Precision.replica; split <;> fun_prop
lemma draw_both : Continuous (fun p: Config G c × Y=> draw F p.1 p.2) := by
       apply continuous_pi; intro i; unfold draw release
       have hh := garment (G:=G) F i
       have hi (i:F.Free) : Continuous (fun y:Y=>windmill F y i) := (continuous_apply _).comp (((weld K).trans (Uniform.tint G _)).continuous)
       exact (G.lieExp_cont.comp ((hi i).comp continuous_snd)).mul (hh.comp continuous_fst)
lemma draw_zero: (1:F.Slice G)=draw F 1 (0:Y):= funext (fun i=> by change (1:G.El)= G.lieExp 0 * replica S.ratio (1:Config G c) (i:F.Free); simp)
lemma sfeed : Tendsto (fun p: Config G c × Y=> draw F p.1 p.2) (𝓝 (1,0)) (𝓝 1) := by rw [draw_zero F]; exact (draw_both F).continuousAt.tendsto
lemma collar_shrinks (hP:Tendsto P (𝓝 0) (𝓝 1)) (hW:Tendsto W (𝓝 0) (𝓝 0)):
    Tendsto (fun p : ℝ×Poll.Body (Precision.Key F G)=> draw F (P p.1) (W p.1+p.2)) (𝓝 0) (𝓝 1):= by
   have ht : Tendsto (fun x : ℝ×Y => W x.1+x.2) (𝓝 0) (𝓝 0):= by rw [← add_zero (0:Y)]; exact (hW.comp continuous_fst.continuousAt.tendsto).add (@continuous_snd ℝ Y _ _).continuousAt.tendsto
   let w: ℝ × Y → Config G c × Y:= fun x=> (P x.1,W x.1+x.2)
   have hs : Tendsto (fun p:ℝ×Y=> P p.1) (𝓝 0) (𝓝 1):= hP.comp continuous_fst.continuousAt.tendsto
   have hw:= hs.prodMk_nhds ht
   change Tendsto ((fun p: Config G c × Y => draw F p.1 p.2) ∘ w) _ _; exact (sfeed (G:=G) F).comp hw

/-- logarithmic coordinates after arbitrary analytic frame operation -/
def retired (t:ℝ)(x:F.Slice G):Y:= ((weld (Precision.Key F G)).trans (Uniform.tint G _)).symm (fun i=> G.plog (G.mat (x i * (floorG F (P t) i)⁻¹))) - W t
set_option maxHeartbeats 120000 in
lemma retreat (hP:Tendsto P (𝓝 0) (𝓝 1)) (hW:Tendsto W (𝓝 0) (𝓝 0)): let N:=𝓝 ((0:ℝ), (1: F.Slice G)); Tendsto (uncurry (retired F P W)) N (𝓝 0) ∧
    ∀ᶠ q in N, draw F (P q.1) (W q.1 + retired F P W q.1 q.2)=q.2:= by
    intro N
    let g (i:F.Free) (q:ℝ×F.Slice G):= q.2 i*(floorG F (P q.1) i)⁻¹
    have hv(i:F.Free): Tendsto (g i) N (𝓝 1):=by
       have he:Tendsto (fun q:ℝ×F.Slice G=> floorG F (P q.1) i) N (𝓝 1) := by
          have hh:floorG F (1:Config G c) i=1:=by unfold floorG; rw [Precision.replica_one]; rfl
          rw [←hh]; exact (garment (G:=G) F i).continuousAt.tendsto.comp (hP.comp continuous_fst.continuousAt.tendsto)
       have h:Tendsto (fun q:ℝ×F.Slice G=> q.2 i) N (𝓝 1):= ((continuous_apply i).comp continuous_snd).continuousAt.tendsto
       simpa [g] using! h.mul he.inv
    let u (q:ℝ×F.Slice G) (i:F.Free):= G.plog (G.mat (g i q))
    have huh:Tendsto u N (𝓝 0):= by
       apply tendsto_pi_nhds.mpr
       intro i; change Tendsto (fun q=> G.plog _) _ (𝓝 (0:G.Color))
       rw [← G.plog_one]; exact G.plog_diff.continuousAt.tendsto.comp ((show Tendsto G.mat (𝓝 1) (𝓝 1) from G.continuous_mat.tendsto 1).comp (hv i))
    let M:= ((weld K).trans (Uniform.tint G _)); constructor
    · have hi:Tendsto (fun q=> M.symm (u q)) N (𝓝 0):=(map_zero M.symm) ▸ (M.symm.continuousAt.tendsto.comp huh)
      have he := hW.comp (show Tendsto Prod.fst N (𝓝 0) from continuous_fst.continuousAt.tendsto)
      have ht : Tendsto (fun q:ℝ×F.Slice G=> M.symm (u q)- W q.1) N (𝓝 (0-(0:Y))):= hi.sub (show Tendsto (fun q:ℝ×F.Slice G=> W q.1) N (𝓝 (0:Y)) from he); rw [sub_zero] at ht; exact ht
    have hx (i:F.Free) : ∀ᶠ q in N,G.lieExp (u q i)=g i q:= (hv i).eventually G.plog_right
    filter_upwards [Filter.eventually_all.mpr hx] with x hv; funext i
    rw [show W x.1+retired F P W x.1 x.2=M.symm (u x) from (by change W x.1+(M.symm (u x)-W x.1)=_; abel)] -- orientation b+(M - b)
    change G.lieExp (M (M.symm (u x)) i) * floorG F _ i=_
    rw [M.apply_symm_apply, show G.lieExp (u x i)=_ from hv i];  simp [g]

variable {P W H} {F': Forest S.ratio} {P' : ℝ → Config G c}{W' : ℝ→Poll.Body (Precision.Key F' G)}{H' : ℝ→F'.Slice G→ℝ}
    {M:ℝ→F.Slice G ≃ᵐ F'.Slice G}
-- only ↑x punctured germ. Path could be nonanalytic, multiple label observables.
lemma opens (hP:Tendsto P (𝓝 0) (𝓝 1)) (hW:Tendsto W (𝓝 0) (𝓝 0))
    (hP':Tendsto P' (𝓝 0) (𝓝 1)) (hW':Tendsto W' (𝓝 0) (𝓝 0))
    (hu:∀ᶠ t in Tested.germ, MeasurePreserving (M t) (F.order G) (F'.order G))
    (hv:Tendsto (fun q:ℝ×F.Slice G=> M q.1 q.2) (𝓝 (0,1)) (𝓝 1))
    (hh:∀ᶠ q in 𝓝 ((0:ℝ),(1:F.Slice G)),0<q.1→H q.1 q.2= H' q.1 (M q.1 q.2))
    (hz:∀ᶠ t in Tested.germ, Integrable (H' t) (F'.order G) ∧ 0≤ H' t):
    FansOut (angle F P W H) (angle F' P' W' H') := by
    obtain ⟨he,hR⟩:= retreat F' P' W' hP' hW'; let A p := draw F (P (Prod.fst p)) (W p.1+p.2); let B (q:ℝ×Y):= (q.1,M q.1 (A q))
    have hA : Tendsto (fun p => (Prod.fst p,A p)) (𝓝 (0:ℝ×Y)) (𝓝 (0,1)):= (@continuous_fst ℝ Y _ _).continuousAt.tendsto.prodMk_nhds (collar_shrinks F P W hP hW)
    have hK : Tendsto B (𝓝 0) (𝓝 (0,1)):= (@continuous_fst ℝ Y _ _).continuousAt.tendsto.prodMk_nhds (hv.comp hA)
    apply Tested.eventually_pos.mono; intro δ hd
    filter_upwards [round _ ((hA.eventually hh).and ((hK.eventually hR).and ((he.comp hK).eventually (ball_mem_nhds _ hd)))),Tested.eventually_pos] with ε Hε hε; filter_upwards [Tested.eventually_small hε, hu,hz] with t ht hU hZ
    let S':=collar F P W ε t; let Z:= collar F' P' W' δ t
    have hh (g) (gh:g∈S') : H t g=H' t (M t g) ∧ M t g∈ Z := by
       unfold S' at gh; rw [enter F _ _ _ _ ht.1] at gh; obtain ⟨y,hy,hG⟩:= gh
       obtain ⟨e1,h1,h2⟩:= Hε t ((abs_lt.mpr ⟨by linarith only [hε,ht.1],ht.2⟩).le) y (mem_closedBall_zero_iff.mp hy)
       rw [← hG]; refine ⟨e1 ht.1,?_⟩; unfold Z; rw [enter _ _ _ _ _ ht.1]; exact ⟨uncurry (retired F' P' W') (B (t,y)), ball_subset_closedBall h2, h1⟩
    unfold angle
    rw [show Fintype.card K=Fintype.card K[F'] from ?_]; swap; · simp only [Precision.Key, Fintype.card_prod]; exact congr_arg (·* Fintype.card G.ColorIndex) (YM.SectorNext.Vacuum.FlatTree.same_free_card F F')
    gcongr
    · exact inv_nonneg.mpr (pow_nonneg ht.1.le _)
    -- set inclusion after coordinate change
    rw [←hU.map_eq,(M t).measurableEmbedding.setIntegral_map _ _]
    change (∫ i in S',H t i ∂ F.order G)≤_
    rw [setIntegral_congr_fun (s:=S') (staying_meas ..) (fun i hi=> (hh i hi).1)]
    apply setIntegral_mono_set ((hU.integrable_comp_emb (M t).measurableEmbedding).mpr hZ.1|>.integrableOn)
    · exact Eventually.of_forall fun i=> hZ.2 _
    exact Eventually.of_forall fun i hi=> (hh i hi).2
end YM.AllOrder.Laplace