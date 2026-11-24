import YM.GradedFar.Bin
/-!
# Same ceiling via signed tests for authentic readings

Uniform length prices; paired tails per those installations. Receding geometry, M.3 authenticated pulse for `m_N`
constant-reference version of actual (uncropped) cutoff moment. Can compare at unrounded points to both S-none and predictions. Packet
cost uses (already shown) continuum comparison, no estimation of m_N derivatives. This
budget is a consequence of earlier results, not requisite for inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h l p k :ℕ}{K:Set (Points n)}{N:Set (Points m)} {U B a η:ℝ}
local notation "g∴"=> strength G
local notation "Γx"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "X♯"=> GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "S•"=> moving G U B
local notation "Y₁"=> atLength F P
local notation "D₁"=> atCenter F P h
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
    (hQ:FullVolume.FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)
variable {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)
variable {q:ℕ}{X E : Type*} [TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X][CompactSpace X][NormedAddCommGroup E][NormedSpace ℝ E]
open MeasureTheory FVA2.GradedFar.Budget

set_option linter.unusedSectionVars false in
lemma symmetric_attends (μ: VectorMeasure X E) [IsFiniteMeasure μ.variation] {L:ℂ→L[ℝ] E→L[ℝ]ℂ}{x:ℝ}{f g:X→ℂ}(hf:Attends μ L x f g): Attends μ L x g f:= by
 refine ⟨hf.2.1,hf.1,?_⟩; rw [norm_sub_rev]; exact hf.2.2
private lemma buys {Y y D N₀ A D' d:X→ℂ}(μ:VectorMeasure X E)[IsFiniteMeasure μ.variation] (B:ℂ→L[ℝ] E→L[ℝ]ℂ) (L:ℝ) (h:Measurable Y)
    (hD:Measurable D)(hN:Measurable N₀)(hA:Measurable A)(hy:Continuous y)(hC:Continuous D')(hv:Continuous d)
    (hQ:∀ i:X,‖Y i-y i‖+‖D i-d i‖+‖Y i-y i-(A i-D' i)‖+‖Y i-N₀ i‖+‖Y i-A i‖≤L):
    Attends μ B L Y y ∧ Attends μ B L D d ∧ Attends μ B L (fun i=> Y i-A i) (fun i=> y i-D' i)∧
      Attends μ B L Y N₀ ∧ Attends μ B L Y A:=by
    have he(u:X→ℂ)(h:Continuous u):μ.Integrable u:= h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)
    have hU(i:X):= (norm_nonneg (Y i-y i)); have hV(i:X):=norm_nonneg (D i-d i); have hh(i:X):=norm_nonneg (Y i-y i-(A i-D' i)); have hz(i:X):=norm_nonneg (Y i-N₀ i); have ht(i:X):=norm_nonneg (Y i-A i)
    have H : Attends μ B L Y y:= closePrice μ B (fun i=> by linarith only [hU i,hV i,hh i,hz i,ht i,hQ i]) h hy.measurable (he _ hy)
    refine ⟨H,closePrice μ B (fun i=>?_ ) hD hv.measurable (he _ hv),closePrice μ B (fun i=>?_ ) (h.sub hA) ((hy.sub hC).measurable) (he _ (hy.sub hC)),
       symmetric_attends μ (closePrice μ B (fun i=>?_ ) hN h H.1), symmetric_attends μ (closePrice μ B (fun i=>?_) hA h H.1) ⟩
    · linarith only [hU i,hV i,hh i,hz i,ht i,hQ i]
    · rw [sub_sub_sub_comm]; linarith only [hU i,hV i,hh i,hz i,ht i,hQ i]
    all_goals rw [norm_sub_rev]; linarith only [hU i,hV i,hh i,hz i,ht i,hQ i]
include hK hx hz
variable (dL:ℝ)
include H
-- keep total variation, not norms of densities. T already mounted unrounded. Can vary s in coordinate s(x).
-- choose supports X with continuous o,x,y, full over ANY signed joint requests (measurable fields z,z',s required). Works even when varying μ etc in each index in the fuse.
theorem maintains (ha:0<a)(H₀:Before_cut F R P Z M ν hd he hh t K N a U η B k p q dL) : ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail,
     ∀ T:ℝ, receding (g∴ r) B a U T → ∀ᶠ i in (again f).fuse,
       ∀ μ:VectorMeasure X E, ∀ [IsFiniteMeasure μ.variation] (L:ℂ→L[ℝ] E→L[ℝ]ℂ),∀ (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1 → Box v 1 → ∀ w:Sec G h,width w≤1 →
       ∀ (x:X→Points n)(y:X→Points m)(o:X→E4), Continuous x → Continuous y→ Continuous o→(∀ j,x j∈K)→(∀ j,y j∈ N)→
       ∀ (s:X→Site (C.side i.1 i.2))(z:X→Positions n)(z':X→Positions m), Readable s→ Readable z → Readable z' →
       (∀ j,RoundedWell C i.1 (x j) (y j) r T (z j) (z' j) (dL*g∴ r^(q+1))) →
       let Y:= fun j=> recite F P r (r*T) (z j) (z' j) (s j) u v
       let D:= fun j=> pulseRow F P h r (r*T) (s j) (z' j) v
       let Fg:= fun j=> appointedH140Crop p (t r) (fullSeries Γx X♯ (-Real.log T) hd he (x j) (y j) u v)
       let Co:= fun j=> croppedResponse Γx X♯ (-Real.log T) hh he (y j) v p (t r)
       let Ynew:= fun j=> packet F P R h (o j) r (x j) u
       let A:= fun j=> croppedVector Γx h p u (x j) (t r)
       let f:= b*g∴ r^k*T^(-(h:ℝ)-η)
       Attends μ L f Y Fg ∧ Attends μ L f (fun j=> D j w) (fun j=> Co j w) ∧ Attends μ L f (fun j=>Y j-D j (A j))
          (fun j=>Fg j-Co j (A j))∧ Attends μ L f Y (fun j=>D j (Ynew j)) ∧ Attends μ L f Y (fun j=>D j (A j)):=by
   obtain ⟨b,hb,H'⟩:= H₀; refine ⟨b,hb,?_⟩; filter_upwards [H',near_collar F R n h hK hx,strength_positive hG] with r hr hc ht T hw
   filter_upwards [hr T hw] with i hi; intro μ hμ L u v hu hv w hW x y o hX hY hO hp hp' s z z' hS hZ hZ' hΦ
   dsimp only; let Q:=fun j=> hi.2.2 (s j) (o j) (x j) (y j) (z j) (z' j) (hp j) (hp' j) (hΦ j);
   have hx' i:= hx (hp i); have he' j: squeeze (-Real.log T) (y j)=T • y j:= by rw [squeeze,neg_neg,Real.exp_log (lt_of_lt_of_le (by positivity : 0 < a*g∴ r^(-B)) hw.1)]
   obtain ⟨hF,hC⟩:= continuous_pair (H.separatedOPE ν).wilson hd he hh hX hY hx' (fun i=>by rw [he' i]; exact (Q i).1) (fun j=>hz (hp' j)) u v p (t r)
   apply buys μ L _ (posted_value (readable_pair s (fun i=>(z i,z' i)) hS (readable_pair z z' hZ hZ')) (fun j=> recite F P r (r*T) j.2.1 j.2.2 j.1 u v))
      (discrete_pairs F P z' s hZ' hS v (fun _=>w) (fun _=> continuous_const) r (r*T)) (discrete_pairs F P z' s hZ' hS v _ (fun j=>packet_coord F R P x o u j hX hO (fun i=> hc (x i) (hp i) (o i))) _ _)
      (discrete_pairs F P z' s hZ' hS v _ (fun j=> fore_coord Z M H ν u j hX hx') _ _) hF hC
   · simp_rw [croppedResponse_apply]; exact (continuous_pair (H.separatedOPE ν).wilson (x:=fun _:X=>(0:Points 1)) (d:=Output h) (fun _=>hh) he hh continuous_const hY (fun _ _ _ _=> Subsingleton.elim ..) (fun i=>by rw [he' i]; exact (Q i).2.1) (fun i=>hz (hp' i)) (fun _=>w) v p (t r)).1
   intro j; refine le_trans ?_ ((Q j).2.2 u v hu hv); simp_rw [LinearMap.sub_apply]; gcongr;
   let e:= pulseRow F P h r (r*T) (s j) (z' j) v-croppedResponse Γx X♯ (-Real.log T) hh he (y j) v p (t r)
   exact (row_le e w).trans ((mul_le_mul_of_nonneg_left hW (norm_nonneg (row e))).trans_eq (mul_one _))
omit hx hz hK H
set_option linter.unusedSectionVars false in
lemma readable_round (r:ℝ)(hr:0<r)(x:X→Points n)(hv:Measurable x): Readable (fun i=> address r (x i)):= fun i=> hv (Extraction.measurable_segment hr i)
end YM.Integration.GradedFar.Auth
