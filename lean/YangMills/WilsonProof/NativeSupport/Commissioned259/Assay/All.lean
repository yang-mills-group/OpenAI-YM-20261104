import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Party
import YangMills.WilsonProof.NativeSupport.Commissioned259.Assay.Test
/-!
# (M.3) as joint tests against any finite complex OR real signed (or more general bilinear)

Same center (allow averaging it over a compact), x (compute c there) and y (T • y only in
formal and M.1 layouts) throughout. No rescaling volume in pair. These test operator ΔM
at each basis direction (so can include all those perturbative labels in joint tests).
Thus the ordinary scope as before; doesn't buy grid-estimator pricing. Continuity receipts and
Borel conditions for these uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Assay
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork Original
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z)
    (hQ:LogTrace F Q.port)

variable {n m z h:ℕ} {L M δ W a b c:ℝ} {d:Fin n→ℕ} {e:Fin m→ℕ}
    {A:Set (Points n)}{B:Set (Points m)}
    (hA:IsCompact A)(h'A:A⊆conf n) (hB:IsCompact B)(h'B:B⊆Outside m)
    (hW:1≤W)(hw:clears W A B) (hM:0≤M)(hδ:0<δ)(hF:Clears W M δ A B)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion O ν
local notation "g"=> g0 G
variable {X I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace X] (μ : VectorMeasure X E) (R : ℂ→L[ℝ] E→L[ℝ] ℂ) (hR: ‖R‖ ≤ 1)
    (Y YX : X→ℂ)(D DX : X→ Sec G h →ₗ[ℂ] ℂ)(packet c': X→ Sec G h)
    [IsFiniteMeasure μ.variation]
  (hd:∀ i,d i ≤ z) (he:∀ i,e i ≤ z) (hh:h ≤ z)
local notation "U" => (measures F Z d e)
open private guest from YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Party
open private full_cont continuity_crop from YangMills.WilsonProof.NativeSupport.Commissioned259.Local
-- pre-inverse. Test ALL the comparisons, with EXACT C evaluations multiplying D
structure Approval (μ:VectorMeasure X E)(R:ℂ→L[ℝ] E→L[ℝ] ℂ)
    (Y YX:X→ℂ)(D DX:X→ Sec G h →ₗ[ℂ] ℂ)(packet c': X→ Sec G h)(p:ℝ) : Prop where
    deltaY : compares μ R Y YX p
    deltaM (i:Toon G h) : compares μ R (fun k=> D k (theory i)) (fun k=> DX k (theory i)) p
    crossed : compares μ R (fun i=> Y i-D i (c' i)) (fun i=> YX i-DX i (c' i)) p
    forecast : compares μ R Y (fun i=> D i (c' i)) p
    retained : compares μ R Y (fun i=> D i (packet i)) p
include hR
section
variable [TopologicalSpace X][OpensMeasurableSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
lemma clear_path (t:ℝ) (p:0≤t)(f:Continuous Y) (gX:Continuous YX)
    (dE : ∀ i:Toon G h, Continuous (fun k=> D k (theory i))) (dX : ∀ i:Toon G h, Continuous (fun k=> DX k (theory i)))
    (hc : ∀ i,Continuous (fun k=> coord i (c' k))) (hw:∀ i, Continuous (fun k=>coord i (packet k)))
    (H:∀ i, checkPrice (Y i) (YX i) (D i) (DX i) (packet i) (c' i) ≤ t) : Approval μ R Y YX D DX packet c' t := by
  simp only [checkPrice] at H
  have he (T:X→Sec G h→ₗ[ℂ]ℂ) {A:X→Sec G h} (ht:∀ i:Toon G h,Continuous (fun k=> T k (theory i))) (hc:∀ i,Continuous (fun k=>coord i (A k))) : Continuous (fun k=> T k (A k)) := by
    rw [show (fun k=> T k (A k))=_ from funext fun k=>beats (T k) (A k)]; exact continuous_finsetSum _ fun i _=> (ht i).mul (hc i)
  have hz(i:X): 0≤ opCost (D i-DX i):= opPos _
  constructor
  · refine owes μ R hR f gX p ?_; intro i; specialize H i; linarith [hz i,norm_nonneg (Y i-YX i - (D i-DX i) (c' i)),norm_nonneg (Y i-D i (packet i)),norm_nonneg (Y i-D i (c' i))]
  · refine fun j=> owes μ R hR (dE j) (dX j) p ?_; intro i; have he : ‖ D i (theory j)-DX i (theory j)‖ ≤ opCost (D i-DX i) := Finset.single_le_sum (fun b _=> norm_nonneg ((D i-DX i) (theory b))) (Finset.mem_univ j)
    apply he.trans; specialize H i; linarith [norm_nonneg (Y i-YX i - (D i-DX i) (c' i)), norm_nonneg (Y i-YX i),norm_nonneg (Y i-D i (packet i)),norm_nonneg (Y i-D i (c' i))]
  · refine owes μ R hR (f.sub (he D dE hc)) (gX.sub (he DX dX hc)) p ?_; intro i
    rw [show Y i- D i (c' i) -(YX i-DX i (c' i))=Y i-YX i-(D i-DX i) (c' i) from (?_)]
    · specialize H i; linarith [norm_nonneg (Y i-YX i),hz i,norm_nonneg (Y i-D i (packet i)),norm_nonneg (Y i-D i (c' i))]
    rw [LinearMap.sub_apply]; abel
  · refine owes μ R hR f (he D dE hc) p ?_; intro i; specialize H i; linarith [norm_nonneg (Y i-YX i),hz i,norm_nonneg (Y i-D i (packet i)),norm_nonneg (Y i-YX i - (D i-DX i) (c' i)) ]
  refine owes μ R hR f (he D dE hw) p ?_; intro i; specialize H i; linarith [norm_nonneg (Y i-YX i),hz i,norm_nonneg (Y i-D i (c' i)),norm_nonneg (Y i-YX i - (D i-DX i) (c' i)) ]
end
include H hA h'A hB hW h'B hw hQ hZ hδ hF hM
-- including every component deltaM; crosses retain **products** with c at x
lemma filled (hL:0≤L) (hn:0<n)
    (paid : Calibrated G t) (S0: StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
    (η:ℝ)(hη:0<η)(dη:η<1)(P:ℕ): ∀ᶠ b:ℝ in atTop, ∀ᶠ p:ℕ in atTop, ∀ a c:ℝ, 0<c→ c≤a →
    Round Vx t U hd he p a b W A B → Round Vx t (measures F Z (fun (_:Fin 1)=>h) e) (fun _=>hh) he p a b W {0} B →
    ∃ C :ℝ, 0<C ∧ ∀ᶠ r in late, ∀ T ≥ W, c*g r^(-b) ≤ T → T ≤ a*g r^(-b) →
      ∀ A':Set E4, IsCompact A' → ∀ u∈Balls L G d, ∀ v∈Balls L G e, ∀ q:Viewers F, ∀ μ:VectorMeasure (↥A' × ↥A × ↥B) E, IsFiniteMeasure μ.variation →
        let o (i:↥A' × ↥A × ↥B) := ((q,i.1.val) : Owner F); let x(i:↥A' × ↥A × ↥B):=i.2.1.val; let y(i:↥A' × ↥A × ↥B):=i.2.2.val
        Approval μ R (fun i=> Original.total F Z d e (o i) r T (x i) (y i) u v)
          (fun i=>crop p (t r) (measurement Vx Bx hd he (x i) (T • y i) (-Real.log T) u v))
          (fun i=> Original.centerD F Z h e (o i) r T (y i) v) (fun i=> predicted Vx Bx he hh (T • y i) (-Real.log T) v p (t r))
          (fun i=> Original.coefficients F Z Q d h (o i) r (x i) u) (fun i=> purchased Vx u (x i) h p (t r))
          (C*T^(-((h:ℝ)+η))*(g r)^P) := by
  have H' := listing F Z Q H hZ hQ hA h'A hB h'B hW hw hM hδ hF hd he hh S0 hL paid P η hη dη hn
  filter_upwards [H'] with b L'; refine L'.2.mono fun p X a c hp ha H0 V=>?_
  obtain ⟨C,hC,E⟩:= X a c hp ha H0 V; have L:= guest F Q (h:=h) hQ hM hδ hF
  refine ⟨C,hC,?_⟩; filter_upwards [L,E,self_mem_nhdsWithin,g0_pos sim] with r L E hr i T hhL hhR z X' hX' u hu v hv q μ h' o x y
  let J:= ↥X' × ↥A × ↥B; let w(i:J):=i.1.val
  have px(i:J): x i∈A:=i.2.1.property; have py(i:J): y i∈B:=i.2.2.property
  have hx: Continuous x:= by unfold x; fun_prop
  have hy: Continuous y:= by unfold y; fun_prop
  have ho: Continuous w:=by unfold w J; fun_prop
  haveI := isCompact_iff_compactSpace.mp hA; haveI := isCompact_iff_compactSpace.mp hB; haveI:= isCompact_iff_compactSpace.mp hX'
  have hT:= zero_lt_one.trans_le (hW.trans hhL)
  refine clear_path μ R hR _ _ _ _ _ _ _ (by positivity) (affection F Z hδ hF x y w hx hy ho px py hr hhL u v q) ?_ ?_ ?_ (pave H h'A x hx px u p) (actual_cw F Z Q x w hx ho u q (h0:=fun i k hk=> L _ (px i) _ (py i) _ k hk)) (fun i=> E T hhL hhR z (x i) (px i) (y i) (py i) (o i) u hu v hv)
  · exact (rows_cont hd he hh ((H.dilation ν).check) ((H.separatedOPE ν).wilson) continuous_const hx hy (fun _=>hT) (fun _ _=>continuous_const) (fun _ _=>continuous_const) (fun i=> hw T hhL _ (px i) _ (py i)) (fun i=> h'B (py i)) (fun i=> h'A (px i)) p (fun _=>t r) continuous_const).1
  · intro i
    have A := @Original.address _ _ _ _ F Z _ _ _ _ _ h'B hW _ _ y w hy ho py _ _ hr hhL v q (fun _=>theory i) (fun i=>continuous_const)
    exact A
  intro i; simp_rw [Comparing.center_read]; exact (continuity_crop _ (full_cont (d:=fun _=>h) (fun (_:Fin 1)=>hh) he ((H.dilation ν).check) ((H.separatedOPE ν).wilson) (T:=fun _=>T) continuous_const continuous_const hy (fun _=>hT) (u:=fun _ _=>theory i) (fun _ _=>continuous_const) (fun _ _=>continuous_const) (fun i=> squeeze_T T hT (y i) ▸ lives (-Real.log T) (h'B (py i)))) p (fun _=>t r) continuous_const)
end YM.FVA2.GradedFar259.Assay
