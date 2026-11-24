import YM.AllOrder.Laplace.Link
/-!
# Identity to actual one-step period polynomial in Local.Pure. Arbitrary T, charts.
 Includes the action, soft prefactors, curved stationary bits, and normalized log.
 No uniform constants, no all-period power estimates here. See one-step `Desk` valuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested MeasureTheory ProbabilityTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical MatrixOrder
open Matrix Finset Lattice Wilson RG Gauge Precision Tree Push Push.Uniform
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat Local Vote PositionX.Jet Planned.JetPort
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
variable (F: Forest S.ratio) (O: ChartRatio G)(k:S.Choices) (U:Pressure.Tube G S)
local notation "p"=> U.high
local notation "R"=> U.up
local notation "K"=>Precision.Key F G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> Apex c G
local notation "A"=> Lapis.table F k R p
variable {C q L :ℝ}{n:ℕ} {ρ : Bid.Dir G c→AxisChart G F} (T:Push.Uniform.Before G q C S.patch.J S.kernel (n+3))
   (hG:Bid.Larger (G:=G) S)(h:(U.up).Bounds U.high q C L)(he:T.Service F U.high U.up ρ)(hO:LocalRatio O)
local notation "W"=> orbit F ρ
local notation "M"=> gram F R p ρ k
local notation "K₀"=> gram F R p ρ k 0
local notation "Ξ"=> mist F O R
local notation "D"=> startup F O k R p T hG h he hO
include hO T h he hG
lemma speck (hp₀:‖(0:Apex c G)‖ < (T.tables (p) S.patch).horizon): ContDiffAt ℝ ω (Lantern.shade (gram F R p ρ k)) 0:= Function.const _ (((Counter.service he h hG rfl rfl k|>.alongShell (x:=0) (mem_ball_zero_iff.mpr hp₀)).whole_log.1.div_const 2)) hO
lemma accent_ready : Accent A Ξ M W:= by
    refine ⟨interest F k R p T hG h he,mist_nice F O R p T h hO,speck F O k U T hG h he hO (norm_zero.trans_lt he.x_pos),?_⟩
    filter_upwards [ball_mem_nhds (0:Apex c G) he.x_pos] with x hx; obtain ⟨hv,-,-,hum⟩:= wakes F k R p ρ q C L T hG h he x (mem_ball_zero_iff.mp hx); exact ⟨hv,fun z=> ⟨heart F k R p ρ q C L T hG h he x (mem_ball_zero_iff.mp hx) z, hum z⟩⟩
variable (x:Apex c G)
local notation "P"=> course x
local notation "L₀"=> (W ∘ course x)
def scaleP := O.scale ^ Fintype.card F.Free * munit (gram F R p ρ k 0)
lemma scale_pos : 0 < scaleP (ρ:=ρ) F O k U:= Function.const _ (Function.const _ (Function.const _ (mul_pos (pow_pos hO.scale _) (munit_pos _)) hG) h) he
lemma predicts : let s := someJ (slopeP P A Ξ M W); let T' := (D).drawdown P L₀
   logS T'= just (Real.log (scaleP (ρ:=ρ) F O k U))+s+logS (wholeP A Ξ M W x):=by
   let r:=1-(D).perk P L₀; let he':= wakes F k R p ρ q C L T hG h he 0 (by simp [he.x_pos]); let L' := course_claim (accent_ready F O k U T hG h he hO) x; intro s T'
   exact stage (accent_ready F O k U T hG h he hO) (O.scale^ Fintype.card F.Free) x r (show _ from (show 0 < (D).perk P L₀+r by unfold r; simp)) he'.2.2.1 (pow_pos hO.scale _)
-- Tensor.diag evaluation log of truncated connectivity = someJ along ray.v
local notation "Φ"=> Pure.hard F U ρ k
local notation "Γ"=> Pure.soft F U O ρ k
local notation "rep"=> Vote.aggregation A Ξ W M
omit hO T h he hG in
-- purely algebra normalization, no spectral receipt for this polynomial
lemma former (i:ℕ) : logS (wholeP A Ξ M W x) i= Radial.jet (Real.log ∘ rep i) i (1,x):= by
 let Y₀:= (1,x); let s:= rep i; let v:= fun t:ℝ=> (Real.log ∘ s) (t • (1,x))
 have ht: ContDiffAt ℝ ω s 0:= (Vote.terms_art _).contDiffAt
 have hk : v=Real.log ∘ PositionX.Jet.delay (wholeP A Ξ M W x) i:= by
    ext1 t; unfold v Function.comp; congr 1
    unfold PositionX.Jet.delay s Vote.aggregation Vote.terms; rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=> ?_
    exact Tensor.homogeneous _ _ _
 change someJ _ i=_; rw [←hk]; exact jet_entry ((Real.contDiffAt_log.mpr (show s 0≠0 from Vote.collect0.trans_ne one_ne_zero)).comp _ ht|>.of_le le_top) _
set_option quotPrecheck false
lemma voted (i:ℕ) : let T' := (D).drawdown P L₀; logS T' i= (just (Real.log (scaleP (ρ:=ρ) F O k U)) + fun i=> Pure.flip F U O ρ k i x) i := by
   let T0:= accent_ready F O k U T hG h he hO; intro T'; change logS ((D).drawdown P L₀) i = just _ i + Pure.flip _ _ _ _ _ _ _; rw [predicts F O k U T hG h he hO x, Pi.add_apply,Pi.add_apply,add_assoc, former]
   unfold Pure.flip; have ht := avows T0 P (course_claim T0 x).cont (course_claim T0 x).p0 0; let a:=enrolling (course x) 0 A W; let b:= dropP P Ξ M W; have hb:= nice_drop T0 P (course_claim T0 x).cont (course_claim T0 x).p0; have hT := interest F k R p T hG h he
   let w : Apex c G→X×Y:=fun t=>(t,W t); have he':w 0=0:=Prod.ext rfl hT.map0
   have hw : ContDiffAt ℝ ω w 0:= contDiffAt_id.prodMk hT.shape; have hg : ContDiffAt ℝ ω Φ 0:= (he'.symm ▸ T0.steer.hard).comp (f:=w) 0 hw; have hz : ContDiffAt ℝ ω Γ 0:= (((he'.symm ▸ T0.poly).comp (f:=w) 0 hw).add T0.alive).sub contDiffAt_const
   have h' j : someJ a j= Radial.jet Φ j x:=by
     rw [show a=(fun t:ℝ=> Φ (t• x)) from funext (fun t=> by unfold a enrolling; rw [smul_zero,add_zero]; rfl)]; exact jet_entry (hg.of_le le_top) _
   have hB i: someJ b i=Radial.jet Γ i x:= jet_entry (h:=Γ) (hz.of_le le_top) _
   rw [show slopeP P A Ξ M W= -climb2 a-b from rfl,some_sub (show ContDiffAt ℝ ω (-climb2 a) 0 from (shifty (shifty ht.2.2)).neg) (show ContDiffAt ℝ ω b 0 from hb), exact_neg (show ContDiffAt ℝ ω (climb2 a) 0 from shifty (shifty ht.2.2)),retrace (h:=a) ht.1 ht.2.1 ht.2.2, Pi.sub_apply, Pi.neg_apply,hB]; erw [h']; rfl -- jet=chip need simp?
omit T h he hG hO in 
lemma nights : Continuous (Desk.night (G:=G) (c:=c)):= by
 let L:= Uniform.tint G (Exterior.Body 1 c); have hp: Continuous (Precision.represent : Bid.Dir G c → Config G c):= by unfold Precision.represent increment Exterior.collect; apply continuous_pi; intro i; fun_prop
 exact hp.comp L.continuous
lemma voted_flat (i:ℕ) : let H:=D; let S' := H.drawdown P (⇑(fderiv ℝ H.quiet 0 ∘L fderiv ℝ (course x) 0)); logS S' i=(just (Real.log (scaleP (ρ:=ρ) F O k U))+ fun i=> Pure.flip F U O ρ k i x) i:=by
   intro H S'
   have hc y (hy:NextTo (D).quiet P y):= Desk.award hG.1 hO (fun t:ℝ=> (show Toll f (primitive R p t) from (toll_main h).add ((toll_loop h).scale (t^2)))) («L»:=D) hy
   let W':= (D).quiet∘ P; have he0:= accent_ready F O k U T hG h he hO; have hh:= course_claim he0 x; have ht := flat_belong he0.steer hh.p0 hh.cont; have hn : Desk.night (0:X)=1:=by unfold Desk.night; rw [_root_.map_zero,link_one]
   have hp : Tendsto ((Desk.night (c:=c) (G:=G)) ∘ (course x)) (𝓝 0) (𝓝 1):= by
      have hg : Continuous (Desk.night (c:=c) (G:=G)):=  nights
      rw [←hn]; exact hg.continuousAt.tendsto.comp (show Tendsto P (𝓝 0) (𝓝 0) from hh.p0 ▸ hh.cont.continuousAt)
   rw [show S'= (D).drawdown P L₀ from confirmed_cross F (ht.w0 ▸ ht.progress.continuousAt) (hh.w0 ▸ hh.progress.continuousAt) hp (hc _ ht) (fun t:ℝ=> (show Toll f (primitive R p t) from (toll_main h).add ((toll_loop h).scale (t^2)))) hG.1 (hc _ hh)]; exact voted F O k U T hG h he hO x i
end YM.AllOrder.Laplace.SigmaP
