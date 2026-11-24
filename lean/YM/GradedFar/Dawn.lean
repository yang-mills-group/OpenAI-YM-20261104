import YM.GradedFar.Attend
import YM.GradedFar.Gentle
/-!
# M3 for the continuum terms at *any* fixed bounding boxes, pairing

An extension of proof of `Attend.responds`. For checks at larger labels also in same joint bank.

Prices inside the same profile and answer for every Sec center field on that joint reading.
For variable parameter/meshes, use the explicit eventual statement. Include pricing on both true
and forecast `c`, which aren't constants on this test, and on the genuine residual `dY-dM c`.
Keeping Jacobian implicit because we don't move any measure to the grown `Ty` variable: all
measures in own `x,y` variables, for example pullback profiles (if specifying densities instead
in `Ty` must include the Far Jacobian in the given test, not claimed for an unchanged density at
those points).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Filter Function Set Spec Table Extraction
open OPE OPE.Orbits
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2 FVA2.O.Enh FVA2.GradedFar FVA2.Scale FVA2.O.Score
open MS MS.Book MS.Fleet MS.Land FVA2.Register MeasureTheory
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}(F:Final C fo S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J:ℝ→tower S)
    {n m l h p p':ℕ} {d:Fin n→ℕ}{e:Fin m→ℕ}
variable (N:WilsonPrescription G){hG:G.Simple}(Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:MS.Land.Prescription (Press.portDeck G)}(H:Main.Match N hG Z σ true)(ν:ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "W" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "g" => strength G
variable {X E:Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {K:Set (Points n)} {S':Set (Points m)}
    {t:ℝ→ℝ} {a Λ β η:ℝ} (hd:AppointedH140Through l d) (he:AppointedH140Through l e) (hh:h≤l)
    (hK:IsCompact K)(hx:K⊆conf n)(hy:S'⊆Outside m) (ha:0<a)
    {R0 E0:ℝ} (Hw:Gentle.BeforeBox F J R N Z ν t hd he hh K S' a Λ η β p' p R0 E0)

open private YM.Integration.GradedFar.five from YM.GradedFar.Attend
private lemma priceRow {Y y:ℂ}{M₀ B: Sec G h →ₗ[ℂ] ℂ}{p q c:Sec G h}{D R:ℝ}(hr:1≤R)(hp:width p≤R)
   (He:‖Y-y‖ + rowPrice (M₀-B) + ‖Y-y-(M₀-B) c‖ + ‖Y-M₀ q‖+ ‖Y-M₀ c‖ ≤ D): ‖Y-y‖ + ‖M₀ p-B p‖+ ‖Y-y-(M₀ c-B c)‖ + ‖Y-M₀ q‖+ ‖Y-M₀ c‖ ≤ D*R:=by
 rw [← LinearMap.sub_apply,← LinearMap.sub_apply]; have h:= (row_le (M₀-B) p).trans (mul_le_mul_of_nonneg_left hp (show 0≤rowPrice (M₀-B) from (row (M₀-B)).opNorm_nonneg))
 refine le_trans ?_ (mul_le_mul_of_nonneg_right He (by positivity)); simp only [add_mul]; let k (u:ℂ):= le_mul_of_one_le_right (norm_nonneg u) hr; exact add_le_add (add_le_add (add_le_add (add_le_add (k _) h) (k _)) (k _)) (k _)
include ha H hK hx hy Hw
set_option maxHeartbeats 400000 in
theorem respondsBox {Q:ℝ}(hQ:1≤ Q) : ∃ L:ℝ,0<L ∧ ∀ᶠ r in trail, ∀ T:ℝ, Budget.receding (g r) β a Λ T →
    ∀ x:X→Points n,∀ y:X→Points m,∀ o:X→E4,Continuous x → Continuous y → Continuous o → (∀ i,x i∈ K) → (∀ i,y i∈S') → ∀ ω:Viewers F,
    ∀ (u:AppointedH140Inputs G d) (v:AppointedH140Inputs G e),Box u R0 → Box v E0 → ∀ (μ:VectorMeasure X E),∀ [IsFiniteMeasure μ.variation],∀ B:ℂ →L[ℝ] E →L[ℝ] ℂ,
      let Y := fun i => atLength F J ω (o i) r T (x i) (y i) u v
      let D := fun i => atCenter F J h ω (o i) r T (y i) v
      let Yx := fun i=> appointedH140Crop p (t r) (fullSeries A W (-Real.log T) hd he (x i) (y i) u v)
      let Dx := fun i=> croppedResponse A W (-Real.log T) hh he (y i) v p (t r)
      let c := fun i=> croppedVector A h p u (x i) (t r)
      let Z := fun i=> packet F J R h (o i) r (x i) u
      let fee := L*(g r)^p'*T^(-(h:ℝ)-η)
      -- c roles & profile identical; all singleton directions *too*. -- scope no MeshPair claims
      ∀ q:Sec G h,width q ≤ Q →
      Attends μ B fee Y Yx ∧ Attends μ B fee (fun i=> D i q) (fun i=> Dx i q) ∧
        Attends μ B fee (fun i=> Y i - D i (c i)) (fun i=> Yx i - Dx i (c i)) ∧
        Attends μ B fee Y (fun i=> D i (Z i)) ∧ Attends μ B fee Y (fun i=>D i (c i)) := by
   obtain ⟨L,hL,Hw⟩:=Hw; refine ⟨L*Q,by positivity,?_⟩
   filter_upwards [near_collar F R n h hK hx,self_mem_nhdsWithin,Hw,strength_positive hG] with r hc (hr:0<r) hw hq' T ht
   intro x y o hX hY hO hp hP ω u v hu hv μ hμ B
   dsimp only; intro q hq
   have hT:0<T:= lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hq' _)) ht.1
   have hA i : forest (x i) (T • y i) ∈ conf (n+m) := (hw T ht (x i) (hp i) (y i) (hP i)).1
   have hV i : outgoing (T • y i) ∈ conf (1+m) := (hw T ht (x i) (hp i) (y i) (hP i)).2.1
   have hν : ∀ i:X,squeeze (-Real.log T) (y i)=T • y i:=fun i=>by rw [squeeze,neg_neg,Real.exp_log hT]
   obtain ⟨hYx,hDx⟩:= continuous_pair (H.separatedOPE ν).wilson hd he hh hX hY
     (fun i=>hx (hp i)) (fun i=> hν i|>.symm ▸ hA i) (fun i=>hy (hP i)) u v p (t r)
   have hR:= continuousPack F R J x y o ω u v hX hY hO hr hA hV (fun i=>hc _ (hp i) (o i))
   apply YM.Integration.GradedFar.five μ B _ (continuousY F J x y o ω u v hX hY hO hr hA) hYx (continuousD F J y o ω v hY hO q hr hV)
      hR (continuousVectorResponse F J x y o ω u v hX hY hO N Z H ν hr hV (fun i=> hx (hp i)) p (t r) h) ?fee hDx
   · simp_rw [croppedResponse_apply]; exact (continuous_pair (H.separatedOPE ν).wilson (x:=fun _:X=>(0:Points 1)) (d:=Output h) (fun _=>hh) he hh
       continuous_const hY (fun _ _ _ _=> Subsingleton.elim ..) (fun i=>hν i|>.symm ▸ hV i) (fun i=>hy (hP i))
       (fun _=>q) v p (t r)).1
   intro i; exact (priceRow hQ hq ((hw T ht (x i) (hp i) (y i) (hP i)).2.2 (o i) ω u v hu hv)).trans_eq (by ring)
end YM.Integration.GradedFar
