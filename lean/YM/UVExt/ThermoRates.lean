import YM.UVExt.ChartPair
import YM.UVExt.LoopCount

/-! At a fixed common grid pair, stationarity and the log-plane comparisons transport the *difference* of loop quadratic jets, up to the existing finite-size exponential tolerance and kinetic coefficient difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Set Filter Matrix Lattice Laurent Tree RG Wilson Precision Exterior Bid
open Tensor Work.F03
open scoped BigOperators Topology ContDiff Classical
variable {G : Gauge} {n : Side} (v : fieldDir G n 1) {M : ℕ→PathData G} {Z : Shadow G} {p : Clip} {σ C Λ : ℝ}
omit v
set_option maxHeartbeats 700000 in
lemma lowSpiral {j : ℕ} (h : Passing M Z σ C Λ p) (he : j≤1) : (h.spiralTensor n j) =0 := by
   refine Tensor.ext_diag _ _ ?_ (by exact fun _ _=>rfl) (funext fun u=> ?_)
   have hr (v) (p : Equiv.Perm (Fin j)) := (h.loop_groomed n).mono fun i hi=> show spray (fun d=>tread n (M d)) j i (v ∘ p)=spray (fun d=>tread n (M d)) j i v from Analysis.sym_Jet (hi.of_le (finite_cap _)) v p
   exact fun v p=> tendsto_nhds_unique (view_cont.continuousAt.tendsto.comp ((h.loopLimit n j |>.1).prodMk_nhds (tendsto_const_nhds (x:=v ∘ p)))) ((view_cont.continuousAt.tendsto.comp ((h.loopLimit n j |>.1).prodMk_nhds (tendsto_const_nhds (x:=v)))).congr' ((hr v p).mono fun i h=>h.symm))
   rw [h.loopLimit n j |>.2]; exact (twin_near _ h).1 j (by omega)
set_option maxHeartbeats 700000 in
lemma joint_base_loop {R : ℕ→PathData G} {Y : Shadow G} {q:Clip} {s K V : ℝ} (h : Passing M Z σ C Λ p) (hr : Passing R Y s K V q) : Junction (fun i=>tread n (M i)) (fun i=>tread n (R i)) 1 := by
   intro j hj
   use h.spiralTensor n j
   have hv : h.spiralTensor n j = hr.spiralTensor n j := by rw [show h.spiralTensor n j=0 from (lowSpiral h hj), show hr.spiralTensor n j=0 from lowSpiral hr hj]
   constructor
   · exact (h.loopLimit ..).1
   rw [hv]; exact ((hr.loopLimit n j).1)


namespace Slab
variable {f c:Side} {S:StepData c f} {g : Ratio c f}
variable {U R : ℕ→PathData G} {p r : Clip} {t : S.Choices} {F : Forest S.ratio} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} {η : ℝ}
    {U' R' η' ρ' Y'} (L : Slab F U R p r t ρ η Y) (V : Slab F U' R' p r t ρ' η' Y')

def perLoop (_ : Slab F U R p r t ρ η Y) i (x : fieldDir G c 1) := Precision.loop (U i) (lifting F (represent x) (ρ i x))
variable {hσ hC hΛ hμ hZ hA uσ uC uΛ uμ uZ uA : ℝ} {K V' K' T : Shadow G} (hU : Passing U K hσ hC hΛ p) (hP : Passing R K' hμ hZ hA r) (hB : Passing U' V' uσ uC uΛ p) (hD : Passing R' T uμ uZ uA r)
include L
private def pathTrial (_:Slab F U R p r t ρ η Y) (w:Dir G c) i := (paired w fun z:ℝ=>ρ i (z • w))
def coilTrial (w : Dir G c) (i : ℕ) : ℝ→Dir G f := L.axis ∘ pathTrial L w i
protected lemma flowPath (w : Dir G c) : lucid (fun i => pathTrial L w i) ∧ Pinned (pathTrial L w) := ⟨L.critical.mono (fun i hi=>(pairSmooth _ (ContDiffAt.comp (g:=ρ i) 0 (show ContDiffAt ℝ ω (ρ i) ((0:ℝ) • w) by simpa only [zero_smul] using hi.2.1) (contDiffAt_id.smul contDiffAt_const))).of_le le_top), L.critical.mono fun i hi=>pairAnchored _ _ (by change ρ i ((0:ℝ)•w)=0; simp_rw [zero_smul]; exact hi.1)⟩
protected lemma markSeq (w : Dir G c) : lucid (coilTrial L w) ∧ Pinned (coilTrial L w) := by
    have ht := (L.flowPath w).2.and (L.flowPath w).1
    refine ⟨?_ , ?_⟩
    · apply ht.mono (fun i h' => ?_); unfold coilTrial; apply ContDiffAt.comp (g:=axisLog F) (f:=pathTrial L w i) 0
      · rw [h'.1]; exact ((inclusion_smooth (G:=G) F).snd).of_le le_top -- ?method
      exact h'.2
    apply ht.mono fun i h=>congrArg (axisLog F (G:=G)) h.1 |>.trans (congr_arg Prod.snd (inclusion_zero F))
include hU
lemma inLoop_rate (w : Dir G c) : lucid (fun (i:ℕ) (z:ℝ)=> perLoop L i (z•w)) ∧ ∀ᶠ i : ℕ in atTop,
    (fun z:ℝ=>perLoop L i (z • w))=ᶠ[𝓝 0] (fun z=> tread f (U i) (coilTrial L w i z)) := by
   have hr : ∀ᶠ i : ℕ in atTop,
      (fun z:ℝ=>perLoop L i (z • w))=ᶠ[𝓝 0] (fun z=>tread f (U i) (coilTrial L w i z)) := ((L.flowPath w).2.and (L.flowPath w).1).mono (fun i hi=> (hi.2.continuousAt.tendsto.eventually (hi.1 ▸ inclusion_works F)).mono fun s hs=> (congr_arg (fun a=>Precision.loop (U i) a) hs.symm)) -- direction of hi.1 subst?
   refine ⟨?_,hr⟩
   exact ((lucid_comp (hU.loop_groomed f) (L.markSeq w).1 (L.markSeq w).2).and hr).mono fun i hi=> hi.1.congr_of_eventuallyEq hi.2

omit hU
include V
lemma mark_joint (v : Dir G c) (ht : Junction L.inFT V.inFT 3) (he : 0<η) (hv : 0 < η') :
    ∃ (B : ℕ→ChartVars F G) (W : ℕ→fieldDir G f 1), (∀ j≤2,Tendsto (fun i=>fish j (coilTrial L v i)) atTop (𝓝 (W j)) ∧ Tendsto (fun i=>fish j (coilTrial V v i)) atTop (𝓝 (W j))) ∧ W 1=stretch F (B 1) ∧ Tendsto (fun i=>(v,relative F (Y i) v)) atTop (𝓝 (B 1)) := by
   obtain ⟨B,hB₁⟩ := responses_joint (L.solves_slab v) (V.solves_slab v) ht he hv (L.vertical_gap he) (V.vertical_gap hv)
   have hN : ContDiffAt ℝ ω L.axis 0 := (inclusion_smooth F (G:=G)).snd
   have hw : Joint 2 (coilTrial L v) (coilTrial V v) := Both_comp (f:=pathTrial L v) (g:=pathTrial V v) (axisLog F) 2
       ⟨(L.flowPath v).1,(V.flowPath v).1,fun i hi=>⟨B i,hB₁ i hi⟩⟩ (a:=(0:_)) (tendsto_const_nhds.congr' ((L.flowPath v).2.mono fun i hi=>hi.symm)) (tendsto_const_nhds.congr' ((V.flowPath v).2.mono fun i hi=>hi.symm)) hN
   choose W hW hW' using fun i : Fin 3=>(hw.2.2 i.val (by omega))
   let D i := if he:i<3 then W ⟨i,he⟩ else stretch F (B i)
   have hz : L.axis = V.axis := rfl
   have hY : Tendsto (fun i=>fish 1 (coilTrial L v i)) atTop (𝓝 (stretch F (B 1))) := by
       simp_rw [fish,iteratedDeriv_one]
       change Tendsto (fun i=>deriv (coilTrial L v i) 0) atTop (𝓝 _) -- fish definally?
       let P := pathTrial L v
       have ht (i) (hu : i ∈ {i | P i 0=0 ∧ ContDiffAt ℝ ∞ (P i) 0}) : deriv (L.axis ∘ P i) 0= fderiv ℝ (Work.F03.axisLog F (G:=G)) 0 (fish 1 (P i)) := by
          have h₁ : DifferentiableAt ℝ (L.axis) (P i (0:ℝ)) := by rw [(hu.1:P i 0=0)]; exact hN.differentiableAt (by simp)
          rw [show _=fderiv _ _ _ _ from ((h₁.hasFDerivAt.comp_hasDerivAt (0:ℝ) (ContDiffAt.differentiableAt hu.2 (n:=∞) (by simp)).hasDerivAt).deriv)]
          rw [show P i 0=0 from hu.1,fish,iteratedDeriv_one]; rfl
       have hg := (fderiv ℝ L.axis 0).continuous.tendsto _ |>.comp (hB₁ 1 (by omega)).1
       rw [show (fderiv ℝ L.axis 0 (B 1))=stretch F (B 1) from ((Push.side (axisLog F) (hN.differentiableAt (by simp)) (B 1)).unique (L.faster ..))] at hg
       exact hg.congr' (((L.flowPath v).2.and (L.flowPath v).1).mono fun i hi=>(ht i hi).symm)
   refine ⟨B,D,fun j hj=> show _ from ?_,?_ ,L.pairedX v (hB₁ 1 (by norm_num)).1⟩
   · unfold D; rw [dif_pos (by omega)]; exact ⟨hW _,hW' _⟩ -- replace
   exact tendsto_nhds_unique (hW _) hY
end Slab
end YM.UVExt.Paths
