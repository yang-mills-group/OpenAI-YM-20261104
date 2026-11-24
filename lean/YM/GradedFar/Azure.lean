import YM.GradedFar.Daybreak
import YM.GradedFar.Moon
/-!
# Pair all the comparison tests on genuine physical responses

Post-inverse value & derivative variants. They use through-horizon direction words; exact centre
can vary; prices are TV. Keep same shape even in comparing `actual` against the other. Physical
read/analysis in compact purchase regions. No claims on entire measures beyond hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Window Tariff Tariff.Sunshine FVA2.GradedFar.Cart
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J P: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)(ν:ℝ)
local notation "V"=>Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {t:ℝ→ℝ} (Ht:Pose F J Z t)(Hp:Prepared F J P Z t)(HL:LogTrace F R.port)
variable {n h d:ℕ}{e:Fin n→ℕ}(he:AppointedH140Through h e)
variable (l:Toon G d)(L:TraceOrder n)(p:ℕ){K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)
-- exact claim centre uniform. derive from result single report
include H Ht Hp HL he
lemma ms_smooth (a:ℝ)(u:AppointedH140Inputs G e): ContDiffOn ℝ ∞ (fun x=> coord l (msVector Z M ν u x p d a)) (conf n):= by
 simp_rw [bookVector Z M H,cargo_crop,crop_eq]; exact ContDiffOn.sum fun i _=> contDiffOn_const.mul (lit F J P R Z M H ν Ht Hp HL l he u i)
omit HL in
lemma ms_small (a:ℝ)(u:AppointedH140Inputs G e): ContDiffOn ℝ ∞ (fun x=> appointedH140Crop p a (msRow Z M ν he u x)) (conf n):= by
 simp_rw [exchanged Z M H,crop_eq]; exact ContDiffOn.sum (fun i _=> contDiffOn_const.mul (smooth_post F J P Z M H Ht Hp _ i))
omit H Ht Hp HL he
lemma centered (u:AppointedH140Inputs G e)(o:E4)(r:ℝ): (fun x=> coord l (packet F P R d o r x u)) = (fun x=> messenger F P R 0 r l x u):=by
 funext x; rw [alarm,packet,packet]; refine congrArg _ (congrArg _ ?_); apply Finset.sum_congr rfl; intro i hi; apply congrArg
 have hy: sites o r x=fun i=>sites 0 r x i + o:= by unfold sites; simp_rw [zero_add]; exact funext fun _=>add_comm ..
 exact Eq.trans (by rw [hy]) ( (by simpa only [zero_add] using R.fresh_transport i.val (sites 0 r x) 0 (labels P r u) o))
lemma centeredG (u:AppointedH140Inputs G e)(o:E4)(v:Viewers F) (r:ℝ)(hr:0<r):EqOn (fun x=> TrueCompact F P v r o x u)
    (fun x=> S.classMoment (spectator F v) e (r•x) (labels P r u)) (conf n) := fun _ hx=> (atTable_within F P v _ u o hr hx).symm

variable {T E : Type*}[TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
include H Ht Hp HL he hK hx
theorem pair_m4 : ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀ o:T→E4,∀ (x:T→Points n)(u:AppointedH140Inputs G e), Continuous x→ (∀ i,x i∈K)→ Box u 1→∀ μ:VectorMeasure T E, ∀ [IsFiniteMeasure μ.variation] (B:ℂ →L[ℝ] E→L[ℝ]ℂ),
    let Y := fun i=> δ L (fun x=> coord l (packet F P R d (o i) r x u)) (x i)
    let D:= fun i=> δ L (fun x=> coord l (msVector Z M ν u x p d (t r))) (x i)
    μ.Integrable Y ∧ μ.Integrable D ∧ ‖(∫ᵛ i,Y i ∂[B; μ]) - (∫ᵛ i,D i ∂[B; μ])‖ ≤ C*(t r)^(p+1)*‖B‖*μ.variation.real univ:= by
 obtain ⟨D,hD,H'⟩:= derivativesOPE_coord F J P R Z M H ν Ht Hp HL l he hK hx L p -- arg order from file: l he hK hx L p
 refine ⟨D,hD,?_⟩; filter_upwards [H',near_collar F R n d hK hx] with r hr h v x u ht hv hu μ T' B
 apply test_difference μ B _ _ (fun i=> hr (v i) _ (hv i) u hu); rotate_left
 · exact continuous_iff_continuousAt.mpr fun i=> ((smooth_δ (conf_open _) (ms_smooth F J P R Z M H ν Ht Hp HL he l p _ u) L).continuousOn.continuousAt ((conf_open n).mem_nhds (hx (hv i)))).comp (ht.continuousAt)
 simp_rw [centered F P R l u]; let X₀:= {x:Points n | arena F R d 0 r x}; have hC:= season_open F R d 0 r n
 have h':ContDiffOn ℝ ∞ (fun x:Points n=> messenger F P R 0 r l x u) X₀:=fun x hx=> (breeze F P R 0 r l x hx u).contDiffWithinAt
 exact continuous_iff_continuousAt.mpr fun i=> ((smooth_δ hC h' L).continuousOn.continuousAt (hC.mem_nhds (h _ (hv i) 0))).comp ht.continuousAt
theorem pair_rows : ∃ D:ℝ,0≤D ∧ ∀ᶠ r in trail,∀ v:Viewers F,∀ o:T→E4,∀ (x:T→Points n)(u:AppointedH140Inputs G e), Continuous x→ (∀ i,x i∈K)→ Box u 1→∀ μ:VectorMeasure T E, ∀ [IsFiniteMeasure μ.variation] (B:ℂ →L[ℝ] E→L[ℝ]ℂ),
    let Y:= fun i=> δ L (fun x=> TrueCompact F P v r (o i) x u) (x i)
    let Q:= fun i=> δ L (fun x=> appointedH140Crop p (t r) (msRow Z M ν he u x)) (x i)
    μ.Integrable Y ∧ μ.Integrable Q ∧ ‖(∫ᵛ i,Y i ∂[B; μ]) - (∫ᵛ i,Q i ∂[B; μ])‖≤ D*(t r)^(p+1)*‖B‖*μ.variation.real univ:=by
 obtain ⟨D,hD,H'⟩:= day F J P R Z M H ν Ht Hp HL he hK hx L p; refine ⟨D,hD,?_⟩; filter_upwards [H',self_mem_nhdsWithin] with r hr (hp:0<r) v o x u hx' he' hu μ T' B
 apply test_difference μ B _ _ (fun i=> hr v (o i) _ (he' i) u hu); rotate_left
 · exact continuous_iff_continuousAt.mpr fun i=> ((smooth_δ (conf_open _) (ms_small F J P Z M H ν Ht Hp he p _ u) L).continuousOn.continuousAt ((conf_open n).mem_nhds (hx (he' i)))).comp hx'.continuousAt
 let f:=fun x: Points n=> S.classMoment (spectator F v) e (r • x) (labels P r u); have H:ContDiffOn ℝ ∞ f (conf n):=kernel_smooth F v hp (fun i=> ⟨e i,assign P r (e i) (u i)⟩)
 rw [show (fun i=>δ L (fun x=> TrueCompact F P v r (o i) x u) (x i))= fun i=>δ L f (x i) from funext (fun i=> δ_congr (conf_open _) (centeredG F P u (o i) v r hp) L (hx (he' i)))]
 exact continuous_iff_continuousAt.mpr fun i=> ((smooth_δ (conf_open _) H L).continuousOn.continuousAt ((conf_open n).mem_nhds (hx (he' i)))).comp hx'.continuousAt
end YM.Integration.GradedFar.Batch
