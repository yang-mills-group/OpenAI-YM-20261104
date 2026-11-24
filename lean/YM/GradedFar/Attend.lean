import YM.GradedFar.Screen
/-!
# M3 at signed profile requests, not just singletons/sup after integrating

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
-- spells individual budget, with integrability guard (compact profiles)
def Attends (μ:VectorMeasure X E) [IsFiniteMeasure μ.variation] (B:ℂ →L[ℝ] E →L[ℝ] ℂ)
    (fee:ℝ) (p q:X→ℂ) : Prop := μ.Integrable p ∧ μ.Integrable q ∧
      ‖(∫ᵛ i, p i ∂[B;μ])-(∫ᵛ i, q i ∂[B;μ])‖ ≤ fee*‖B‖*μ.variation.real univ

variable {K:Set (Points n)} {S':Set (Points m)}
    {t:ℝ→ℝ} {a Λ β η:ℝ} (hd:AppointedH140Through l d) (he:AppointedH140Through l e) (hh:h≤l)
    (hK:IsCompact K)(hx:K⊆conf n)(hy:S'⊆Outside m) (ha:0<a)
    (Hw:BeforeInverse F J R N Z ν t hd he hh K S' a Λ η β p' p)

-- help all five comparisons via single proof of uneven integrand and price. Family all μ one window.
private lemma five {Y y D N₀ C D' d : X→ℂ} (μ:VectorMeasure X E) [IsFiniteMeasure μ.variation]
    (B:ℂ →L[ℝ] E →L[ℝ] ℂ)(L:ℝ) (h₀:Continuous Y)(h₁:Continuous y)(hD:Continuous D)(hN:Continuous N₀)
    (hC:Continuous C)(hA:∀ i, ‖Y i-y i‖+ ‖D i - d i‖+ ‖(Y i-y i)-(C i-D' i)‖ + ‖Y i-N₀ i‖ +‖Y i-C i‖ ≤ L)
    (hE:Continuous D')(hp:Continuous d) : Attends μ B L Y y ∧ Attends μ B L D d ∧ Attends μ B L (fun i=> Y i-C i) (fun i=> y i-D' i) ∧
      Attends μ B L Y N₀ ∧ Attends μ B L Y C := by
  refine ⟨test_difference μ B h₀ h₁ (fun i=> ?_),test_difference μ B hD hp (fun i=>?_ ),
     test_difference μ B (h₀.sub hC) (h₁.sub hE) (fun i=>?_), test_difference μ B h₀ hN (fun i=>?_ ),test_difference μ B h₀ hC (fun i=>?_)⟩
  all_goals
    apply le_trans ?_ (hA i)
    try simp only [Pi.sub_apply]
    try rw [show Y i-C i-(y i-D' i)=_ from sub_sub_sub_comm (Y i) (C i) _ _]
    generalize Y i-y i=A'; generalize D i-d i=M'; generalize (A'-(C i-D' i))=F'; generalize Y i-N₀ i=W'; generalize Y i-C i=K'
    linarith only [norm_nonneg A',norm_nonneg M',norm_nonneg F',norm_nonneg W',norm_nonneg K']

include ha H hK hx hy Hw
set_option maxHeartbeats 400000 in
theorem responds : ∃ L:ℝ,0<L ∧ ∀ᶠ r in trail, ∀ T:ℝ, Budget.receding (g r) β a Λ T →
    ∀ x:X→Points n,∀ y:X→Points m,∀ o:X→E4,Continuous x → Continuous y → Continuous o → (∀ i,x i∈ K) → (∀ i,y i∈S') → ∀ ω:Viewers F,
    ∀ (u:AppointedH140Inputs G d) (v:AppointedH140Inputs G e),Box u 1 → Box v 1 → ∀ (μ:VectorMeasure X E),∀ [IsFiniteMeasure μ.variation],∀ B:ℂ →L[ℝ] E →L[ℝ] ℂ,
      let Y := fun i => atLength F J ω (o i) r T (x i) (y i) u v
      let D := fun i => atCenter F J h ω (o i) r T (y i) v
      let Yx := fun i=> appointedH140Crop p (t r) (fullSeries A W (-Real.log T) hd he (x i) (y i) u v)
      let Dx := fun i=> croppedResponse A W (-Real.log T) hh he (y i) v p (t r)
      let c := fun i=> croppedVector A h p u (x i) (t r)
      let Z := fun i=> packet F J R h (o i) r (x i) u
      let fee := L*(g r)^p'*T^(-(h:ℝ)-η)
      -- c roles & profile identical; all singleton directions *too*. -- scope no MeshPair claims
      ∀ q:Sec G h,width q ≤ 1 →
      Attends μ B fee Y Yx ∧ Attends μ B fee (fun i=> D i q) (fun i=> Dx i q) ∧
        Attends μ B fee (fun i=> Y i - D i (c i)) (fun i=> Yx i - Dx i (c i)) ∧
        Attends μ B fee Y (fun i=> D i (Z i)) ∧ Attends μ B fee Y (fun i=>D i (c i)) := by
   obtain ⟨L,hL,Hw⟩:=Hw; refine ⟨L,hL,?_⟩
   filter_upwards [near_collar F R n h hK hx,self_mem_nhdsWithin,Hw,strength_positive hG] with r hc (hr:0<r) hw hQ T ht
   intro x y o hX hY hO hp hP ω u v hu hv μ hμ B
   dsimp only; intro q hq
   have hT:0<T:= lt_of_lt_of_le (mul_pos ha (Real.rpow_pos_of_pos hQ _)) ht.1
   have hA i : forest (x i) (T • y i) ∈ conf (n+m) := (hw T ht (x i) (hp i) (y i) (hP i)).1
   have hV i : outgoing (T • y i) ∈ conf (1+m) := (hw T ht (x i) (hp i) (y i) (hP i)).2.1
   have hν : ∀ i:X,squeeze (-Real.log T) (y i)=T • y i:=fun i=>by rw [squeeze,neg_neg,Real.exp_log hT]
   obtain ⟨hYx,hDx⟩:= continuous_pair (H.separatedOPE ν).wilson hd he hh hX hY
     (fun i=>hx (hp i)) (fun i=> hν i|>.symm ▸ hA i) (fun i=>hy (hP i)) u v p (t r)
   have hR:= continuousPack F R J x y o ω u v hX hY hO hr hA hV (fun i=>hc _ (hp i) (o i))
   apply five μ B _ (continuousY F J x y o ω u v hX hY hO hr hA) hYx (continuousD F J y o ω v hY hO q hr hV)
      hR (continuousVectorResponse F J x y o ω u v hX hY hO N Z H ν hr hV (fun i=> hx (hp i)) p (t r) h) ?fee hDx
   · simp_rw [croppedResponse_apply]; exact (continuous_pair (H.separatedOPE ν).wilson (x:=fun _:X=>(0:Points 1)) (d:=Output h) (fun _=>hh) he hh
       continuous_const hY (fun _ _ _ _=> Subsingleton.elim ..) (fun i=>hν i|>.symm ▸ hV i) (fun i=>hy (hP i))
       (fun _=>q) v p (t r)).1
   intro i; apply le_trans ?_ ((hw T ht (x i) (hp i) (y i) (hP i)).2.2 (o i) ω u v hu hv)
   simp_rw [LinearMap.sub_apply]; gcongr; let V:=atCenter F J h ω (o i) r T (y i) v - croppedResponse A W (-Real.log T) hh he (y i) v p (t r)
   apply (row_le V q).trans; exact (mul_le_mul_of_nonneg_left hq (show 0≤rowPrice V from (row V).opNorm_nonneg)).trans_eq (by ring)
end YM.Integration.GradedFar
