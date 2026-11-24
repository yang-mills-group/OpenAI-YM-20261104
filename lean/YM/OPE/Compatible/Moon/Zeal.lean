import YM.OPE.Compatible.Niche.Derma
import YM.OPE.Compatible.Lake.Fountain
/-! # limits over mesoscopic tape. unaffected period order. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Luke
open Function Filter Set Lattice RG MeasureTheory ContDiff Next.Free Votive Precision Stroke Owl
open Dial
open scoped Topology BigOperators Classical
variable {G:Gauge}{H:Sponsor G}{T:Seasons H}{a:Axis}{g:G.Simple}{C:ChartRatio G}{h:LocalRatio C}{L:PriceBook h T}
variable {Λ : Register G}{S:Table Λ}{l:ℕ}{s:S.RealSpin}(U:Foyer L g a l (ranksT l))(hp:Maxwell.Ranks S s)
include hp
lemma Queen : Module.finrank ℂ (S.Field l)=Module.finrank ℂ (Semester U):=by
       let P:= U.pay.st; obtain ⟨V⟩:= φField U.pay.policy hp; let X: S.Field l ≃ₗ[ℝ] Semester U:= V.trans (Garm (dims U)); have hx:= X.finrank_eq; have h:= Module.finrank_mul_finrank ℝ ℂ (S.Field l); have he:= Module.finrank_mul_finrank ℝ ℂ (Semester U); rw[Complex.finrank_real_complex] at h he; omega
omit hp
section
variable {I E F Q:Type} {u:ℝ}{φ:Filter I} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup Q] [NormedSpace ℂ E][NormedSpace ℂ F][NormedSpace ℂ Q]
variable {c:I→ E →L[ℂ] F}{d:I→ F→L[ℂ] Q}{e:E→L[ℂ] F}{f:F→L[ℂ] Q}
lemma pulp (h:Tendsto c φ (𝓝 e))(hv:Tendsto d φ (𝓝 f)):Tendsto (fun i=> (d i).comp (c i)) φ (𝓝 (f.comp e)):= (ContinuousAt.clm_comp (continuous_fst.tendsto (f,e)) (continuous_snd.tendsto _)).tendsto.comp (hv.prodMk_nhds h)
lemma arcing (h:Tendsto c φ (𝓝 e)) (x:E) : Tendsto (fun i=> c i x) φ (𝓝 (e x)):= ((show Continuous fun y : E→L[ℂ]F => y x from (ContinuousLinearMap.apply ℂ F x).continuous).continuousAt).tendsto.comp h
variable (A:Ultrafilter I)
omit [NormedSpace ℂ E] in
lemma chant [ProperSpace E] {f:I→ E}(h:∀ᶠ i in A,‖f i‖ ≤ u): ∃ x:E,Tendsto f A (𝓝 x):=by
       have hj: Metric.closedBall (0:E) u ∈ Ultrafilter.map f A:= (show ∀ᶠ i in (A:Filter I), f i ∈ Metric.closedBall (0:E) u from h.mono fun i hi=> by rwa [Metric.mem_closedBall,dist_zero_right]); obtain ⟨x,hx,hv⟩:= (isCompact_closedBall (0:E) u).ultrafilter_le_nhds' _ hj; exact ⟨x,hv⟩
end
end YM.OPE.Luke
