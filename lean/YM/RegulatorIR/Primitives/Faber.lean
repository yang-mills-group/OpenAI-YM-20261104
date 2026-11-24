import YM.RegulatorIR.Primitives.Infer
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio

/-!
# log Haar fees per link
No global equality outside chart. Use even extension to have true orbit weight.
Combine finite connected step signatures. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Geometry.Field Chart Gauge RG Orb Laplace Tree Forest
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {I J X:Type}{G:Gauge}{f c:Side}

def ent (G:Gauge):G.Color→ ℝ:= fun x=> Real.log (fee (tray G) x/fee (tray G) 0)
def entry (G:Gauge):G.Color→ ℝ:= fun x=> (ent G x+ent G (-x))/2
lemma touch (G:Gauge) : 0<fee (tray G) 0:= by unfold fee; rw [(traySpec G).anchored,mul_one, max_eq_left (traySpec G).scale.le]; exact (traySpec G).scale
lemma ent_zero : entry G 0=0:=by simp [entry,ent, (touch G).ne']
lemma ent_even (G:Gauge)(u):entry G (-u)=entry G u:=by unfold entry;rw [neg_neg,add_comm]
lemma genuine (G:Gauge) : entry G =ᶠ[𝓝 0] ent G:= by
 filter_upwards [Metric.ball_mem_nhds (0:G.Color) (traySpec G).patch] with i hi
 have hx := Next.SectorChange.ratio_even (traySpec G) hi; unfold ent entry -- order
 rw [show ent G (-i)= Real.log _ from rfl]; unfold ent; unfold fee;rw [←hx];ring
lemma ent_smooth (G:Gauge) : ContDiffAt ℝ ∞ (entry G) 0:= by
 have hp:= ((Chart.Ratio.fee_smooth (traySpec G)).div contDiffAt_const (touch G).ne').log (show fee (tray G) (0:G.Color)/fee (tray G) (0:G.Color) ≠ 0 from ne_of_gt (div_pos (touch G) (touch G)))
 exact (hp.of_le le_top).congr_of_eventuallyEq (genuine G)
lemma valued (G:Gauge) : ∀ᶠ x:G.Color in 𝓝 0,fee (tray G) x = fee (tray G) 0*Real.exp (entry G x):=by
 filter_upwards [genuine G,(Chart.Ratio.fee_smooth (traySpec G)).continuousAt.eventually (lt_mem_nhds (touch G))] with x hx h
 rw [hx,ent,Real.exp_log (div_pos (show 0 < fee _ x from h) (touch G))];field_simp [(touch G).ne']

section Hair
variable (S:StepData c f)(F:Forest S.ratio)

def carnal (i:Edge Cover):Micro (KFoot G):= fun _ x=> if Field.branch F (resolve f i) then 0 else entry G (timber G (x ∘ Sum.inl) i)
lemma carnal_o {P l R:ℝ}(h:Even f.val)(hi:l*f.val=P)(he:Even c.val)(hv:R*c.val=P): Offset (Step.combine (Carto G l P h hi) (Carto G R P he hv)) (posMarch h) (carnal S F):= by
 intro d y t w; unfold carnal;rw [pos_rips,court_in];split
 · rfl
 rw [show _ ∘ Sum.inl=toolP (Carto G l P h hi) d (w ∘ Sum.inl) from rfl,timber_tool]; cases d <;> simp [Motion.sign,ent_even]
lemma rooted (i: Edge Cover):Nonempty (Run (carnal (G:=G) S F i)):=by
 let p:G.ColorIndex↪ KFoot G:= ⟨fun a=> .inl (i,a), fun x y h=> congr_arg Prod.snd (Sum.inl.inj h)⟩
 refine ⟨{ J:= G.ColorIndex, fin:=inferInstance, inc:=p,script:=fun v=>if Field.branch F (resolve f i) then 0 else entry G (WithLp.toLp 2 v.2), smooth:=?_,reaches:=fun _ _=>rfl }⟩
 split_ifs
 · exact contDiffAt_const
 let L : (ℝ × (G.ColorIndex→ℝ))→ₗ[ℝ] G.Color:=(WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).symm.toLinearMap.comp (LinearMap.snd _ _ _); exact (show ContDiffAt ℝ ∞ (entry G) (L 0) from (map_zero L).symm ▸ ent_smooth G).comp (f:=L) _ L.toContinuousLinearMap.contDiff.contDiffAt
lemma carnal_z (G:Gauge)(i t): carnal S F (G:=G) i t 0=0:=by unfold carnal; split;rfl;exact ent_zero
end Hair

variable (G) (I) [Fintype I]
lemma scented (z:Meadow G I): ∀ᶠ t in 𝓝 (0:ℝ), Chart.jacobian (tray G) (t • z)= morning G I * Real.exp (∑ i,entry G (t • z i)):=by
 have hx (i:I): Tendsto (fun t:ℝ=> t • z i) (𝓝 0) (𝓝 0):= by simpa using (show Continuous (fun t:ℝ=> t • z i) from continuous_id.smul continuous_const).tendsto 0
 filter_upwards [eventually_all.mpr fun i=>(hx i).eventually (valued G)] with t h
 unfold Chart.jacobian; simp only [Pi.smul_apply]; simp_rw [h, Real.exp_sum]; rw [Finset.prod_mul_distrib];rfl

def psyche (z:Meadow G I)(t:ℝ):= ∑ i,entry G (t • z i)
lemma psyche_sum (z:Meadow G I): tale (psyche I G z)=∑ i,tale fun t:ℝ=>entry G (t • z i):=by
 rw [show psyche I G z= ∑ i:I, fun t:ℝ=>entry G (t • z i) from (by ext t; simp only [psyche, Finset.sum_apply])]
 rw [tale_sum]; intro i _; exact (show ContDiffAt ℝ ∞ (entry G) ((0:ℝ) • z i) from (zero_smul ℝ (z i)).symm ▸ ent_smooth G).comp (f:=fun t:ℝ=>t • z i) 0 (contDiffAt_id.smul contDiffAt_const)
lemma psyche_zero (z:Meadow G I): (psyche I G z 0)=0:=by simp [psyche, ent_zero]
lemma psyche_smooth (z:Meadow G I) : ContDiffAt ℝ ∞ (psyche I G z) 0:= by
 exact ContDiffAt.sum (fun i _=> (show ContDiffAt ℝ ∞ (entry G) ((0:ℝ) • z i) from (zero_smul ℝ (z i)).symm ▸ ent_smooth G).comp (f:=fun t:ℝ=>t • z i) 0 (contDiffAt_id.smul contDiffAt_const))
-- positive jets calibration of the actual jacobian
lemma spirit (z:Meadow G I): tale (fun t:ℝ=> Chart.jacobian (tray G) (t • z))=PowerSeries.C (morning G I)*expo (tale (psyche I G z)):=by
 let g:= psyche I G z; let c:=morning G I;have hs: ContDiffAt ℝ ∞ g 0:=psyche_smooth I G z
 let f:ℝ→ℝ:= fun t=> c*Real.exp (g t); rw [tale_eq (g:=fun t:ℝ=> Chart.jacobian (tray G) (t • z)) (f:=f) (contDiffAt_const.mul hs.exp) (scented I G z), show f=(fun _=>c)*(fun t=> Real.exp (g t)) from rfl,tale_mul (g:=fun t=>Real.exp (g t)) contDiffAt_const hs.exp,tale_const,tale_ex (f:=g) (psyche_zero ..) hs]
end YM.RegulatorIR.Prim
