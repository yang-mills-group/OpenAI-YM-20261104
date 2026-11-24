import YM.UVExt.ThermoRates

/-! One period pair through the loop transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths.Slab
open Function Set Filter Matrix Lattice Laurent Tree RG Wilson Precision Exterior Bid Tensor Work.F03
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge}
variable {f c:Side} {S:StepData c f} {g : Ratio c f}
variable {U R : ℕ→PathData G} {p r : Clip} {t : S.Choices} {F : Forest S.ratio} {ρ : ℕ→fieldDir G c 1 → AxisChart G F}
    {Y : ℕ→Matrix (Body 1 f) (Body 1 c) ℝ} {η : ℝ}
    {U' R' η' ρ' Y'} (L : Slab F U R p r t ρ η Y) (V : Slab F U' R' p r t ρ' η' Y')

variable {hσ hC hΛ hμ hZ hA uσ uC uΛ uμ uZ uA : ℝ} {K V' K' T : Shadow G} (hU : Passing U K hσ hC hΛ p) (hP : Passing R K' hμ hZ hA r) (hB : Passing U' V' uσ uC uΛ p) (hD : Passing R' T uμ uZ uA r)
include L V hB hU
lemma inLoop_transfer {Y0 : Matrix (Body 1 f) (Body 1 c) ℝ} (he : 0 < η) (h : 0 < η') (w : Dir G c) (hY : Tendsto Y atTop (𝓝 Y0))
   (ht : Junction L.inFine V.inFine 3) : Tendsto (fun i=> fish 2 (fun z : ℝ=>L.perLoop i (z • w)) - fish 2 (fun z:ℝ=> V.perLoop i (z•w))) atTop (𝓝 (discrep (hU.spiralTensor f 2) (hB.spiralTensor f 2) (polish Y0 w))) := by
   obtain ⟨B,W,hW,hZ,hP⟩:=mark_joint L V w (L.track ht (hU.groomed _) (hB.groomed _)) he h
   let z := L.coilTrial w; let z' := V.coilTrial w

   let Δ := discrep (hU.spiralTensor f 2) (hB.spiralTensor f 2)
   have hC : Continuous Δ := (show Continuous (Tensor.diagonal (hU.spiralTensor f 2)) from ((hU.spiralTensor f 2).cont).comp (continuous_pi (A:=fun (_i:Fin 2)=>Dir G f) fun _=>continuous_id)).sub (((hB.spiralTensor f 2).cont).comp (continuous_pi fun (_i:Fin 2)=>continuous_id))
   have hu k := view_cont.continuousAt.tendsto.comp ((hU.loopLimit f 2 |>.1).prodMk_nhds (tendsto_const_nhds (x:=k)))
   have hh k := view_cont.continuousAt.tendsto.comp ((hB.loopLimit f 2 |>.1).prodMk_nhds (tendsto_const_nhds (x:=k)))
   have hh₁ : Tendsto (fun i=>Tensor.diagonal (spray (fun k=>tread f (U k)) 2 i) (W 1) - Tensor.diagonal (spray (fun k=>tread f (U' k)) 2 i) (W 1)) atTop (𝓝 (Δ (W 1))) := (hu fun _=> W 1).sub (hh _)
   have hw := faa_lead (k:=2) (d:=Δ (W 1)) (p:=z) (p':=z') (hU.loop_groomed f) (hB.loop_groomed f) (L.markSeq w).1 (V.markSeq w).1 (L.markSeq w).2 (V.markSeq w).2 (joint_base_loop hU hB) (by omega:1≤2) W ⟨hU.spiralTensor f 2,(hU.loopLimit f 2).1⟩ ⟨hB.spiralTensor f 2,(hB.loopLimit f 2).1⟩ (fun i hi=>hW i hi) hh₁
   have hs : Continuous (stretch (S:=S) (G:=G) F) := by
      rw [show (stretch (G:=G) F)= ((fun x =>(fderiv ℝ (Work.F03.inclusion F (G:=G)) 0 x).2)) from (funext fun x=>Eq.symm (congr_arg Prod.snd (inclusion_deriv F (G:=G) x)))]
      fun_prop
   have hv := ((hC.comp hs).tendsto _).comp hP
   have hg := (hC.tendsto _).comp (polish_tends w hY)
   have hZ' : Δ (stretch F (B 1))=Δ (polish Y0 w) := tendsto_nhds_unique hv (hg.congr fun i=> ?_)
   · change Tendsto _ atTop (𝓝 (Δ _)); rw [←hZ',←hZ]; exact hw.congr' (((inLoop_rate L hU w).2.and (inLoop_rate V hB w).2).mono fun i hi=>congr_arg₂ (·-·) ((hi.1.iteratedDeriv 2).eq_of_nhds.symm) ((hi.2.iteratedDeriv 2).eq_of_nhds.symm))
   · obtain ⟨k,hk⟩ := relativeGauge F (Y i) w
     change _= Δ (stretch (S:=S) F _); rw [hk]; exact loop_null_gauge hU hB 2 (polish (Y i) w) (by omega) k (joint_base_loop hU hB)
end YM.UVExt.Paths.Slab
