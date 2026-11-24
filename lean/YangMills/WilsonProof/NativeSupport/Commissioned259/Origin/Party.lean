import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Marker
/-!
# Continuation also on joint position-test uses (M.3)

Physical counterparts and pre-inverse differences. Analytic pairing by **any** finite signed
complex-test variation on true x and y shapes & optionally center o in any compact. Doesn't
move the Far density. One common Viewer (any phase allowed, no dependence in constants). Same
estimates before comparing the Gram with its inverse. Don't sample fields/deform geometry just
on D. Not proving assertion here about mixing in weak-* topology of states or implementing
histograms; this is continuum estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

variable {n m z h:ℕ} {L M δ W a b c:ℝ} {d:Fin n→ℕ} {e:Fin m→ℕ}
    {A:Set (Points n)}{B:Set (Points m)}
    (hA:IsCompact A)(h'A:A⊆conf n) (hB:IsCompact B)(h'B:B⊆Outside m)
    (hW:1≤W)(hw:clears W A B) (hM:0≤M)(hδ:0<δ)(hF:Clears W M δ A B)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion O ν
local notation "g"=> g0 G

-- One useful assay. Continue to M.3 pairs: read the true marker D twice with c_W and c
-- respectively, keep same Y and w in each. Show both differences within spec.
local notation "S0" => (measures F Z d e)
local notation "S1" => (measures F Z (fun (_:Fin 1)=>h) e)

include hQ hF hM hδ
private lemma guest : ∀ᶠ r in late, ∀ x∈A,∀ y∈B,∀ o:E4,∀ k ≤ h, orbitMargin Q.port k (position o r x) o := by
  let I:=ℝ × ↥A × ↥B × E4; let r(i:I):=i.1; let o(i:I):=i.2.2.2
  let X:= Filter.comap r late; have H':Tendsto r X late:= tendsto_comap
  let x i:=position (o i) (r i) i.2.1.val
  have e':∀ᶠ i in X, WithinRoom (r i) M δ (x i) (o i) := by
    filter_upwards [H'.eventually self_mem_nhdsWithin] with i h; have hx:= hF _ i.2.1.property _ i.2.2.1.property W le_rfl (r i) h
    exact only_room _ hx.length hx.close hx.separation
  have v:= eventually_all.mpr (fun i:Fin (h+1)=> Flash259HorizonFork.margin F hM hδ hQ.toSingleLog H' e' i)
  exact (eventually_comap.mp v).mono fun r p x hx y hy o k h' => p (r,⟨x,hx⟩,⟨y,hy⟩,o) rfl ⟨k,Nat.lt_succ_of_le h'⟩

variable {I : Type} [TopologicalSpace I] (x:I→Points n)(y:I→Points m)(o:I→ E4) (cx:Continuous x)(cy:Continuous y)(co:Continuous o)
    (gx:∀ i,x i∈A)(gy:∀ i,y i∈B) {r T:ℝ}(hr:0<r) (ht:W≤T)
    (u:Slots G d)(v:Slots G e) (p : Viewers F)
local notation "U" => (fun i=>total F Z d e (p,o i) r T (x i) (y i) u v)
local notation "Domx" => (fun i=>centerD F Z h e (p,o i) r T (y i) v)
omit hQ hF hM hδ
private lemma ast {I' J':Type} [Fintype I'][Fintype J']{x:I→ I'→E4}{y:I→ J'→E4} {d:I'→ℕ}{e':J'→ℕ} (u:Labels S d)(v:Labels S e') (h: Continuous x)(v':Continuous y) (hi:∀ i,Injective (beside (x i) (y i))) :
    Continuous (fun i=> Orbits.whole (spectator F p) (x i) u (y i) v) := by
  let f i := beside (x i) (y i)
  have hc:Continuous f := continuous_pi fun i=> by rcases i with i|i; exact (continuous_apply i).comp h; exact (continuous_apply i).comp v'
  simp_rw [ Orbits.whole_observed ]; exact continuous_iff_continuousAt.mpr fun i=>(smooth_observe (spectator F p) (spectate ..).smooth _ (hi i)).comp (f:=f) (x:=i) hc.continuousAt
include cx cy co gx gy hF hδ hr ht in
lemma affection : Continuous U := by
  simp_rw [total_eq]; refine ast F p _ _ (continuous_pi fun i=>by unfold position; fun_prop) (continuous_pi fun i=>by unfold position; fun_prop) (fun i=>profiles (o i) (hF _ (gx i) _ (gy i) T ht r hr) hδ)
include cy co gy h'B ht hr hW in
lemma address {f:I→ Sec G h} (hp:∀ i, Continuous (fun r=> coord i (f r))) : Continuous (fun i=> Domx i (f i)) := by
  rw [show (fun i=> Domx i (f i))= _ from funext fun i=> beats (Domx i) (f i)]
  refine continuous_finsetSum _ fun b _=> Continuous.mul ?_ (hp b)
  have hP:0<T:=zero_lt_one.trans_le (hW.trans ht)
  simp_rw [center_upon F Z e _ hr hP (h'B (gy _)),LinearMap.comp_apply]; refine ast F p (d:=fun (_:Unit)=>h) _ _ (continuous_pi fun i=> co) (continuous_pi fun i=> by unfold position; fun_prop) (fun i=> ?_)
  -- Need Injective beside (sole o) pos. Center param continuity not translation.
  let V := beside_separate (x:=(0:Points 1)) (T:=T) (y:=y i) (squeeze_T T hP (y i) ▸ lives (-Real.log T) (h'B (gy i))) hr (o i)
  obtain ⟨hi,hj,h⟩:= beside_distinct.mp V; exact beside_distinct.mpr ⟨injective_of_subsingleton _,hj,fun i j=> by convert h 0 j; simp [sole,position]⟩

include cx H gx h'A
lemma pave (q:ℕ) : ∀ b: Toon G h, Continuous (fun i=> coord b (purchased Vx u (x i) h q (t r))) := by
  intro b; simp_rw [coin,crop_apply]; refine continuous_finsetSum _ fun k _=>continuous_const.mul ?_
  exact coeff_continuous (H.separatedOPE (0:ℝ)).wilson (u:=fun i=>u) cx (fun _ _=> continuous_const) (fun i=>h'A (gx i)) ..
omit H gx h'A
include cy
-- B-coef packet from `Reader.fresh_smooth` on genuine orbitMargin; use only continuity in x here
omit cy in
include co in
lemma actual_cw {h0 : ∀ i,∀ k ≤ h,orbitMargin Q.port k (position (o i) r (x i)) (o i)} : ∀ b : Toon G h, Continuous (fun i=>coord b (coefficients F Z Q d h (p,o i) r (x i) u)) := by
  let g' i:=position (o i) r (x i); let L (b:Toon G h):= LinearMap.toContinuousLinearMap ((coord b).comp (frame Z r h).symm.toLinearMap)
  intro b; refine (L b).continuous.comp (show Continuous (fun i=> Q.packet h (g' i) (own Z r u) (o i)) from ?_)
  unfold Reader.packet
  refine continuous_finsetSum _ fun j _=> ((F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)).continuous_of_finiteDimensional.comp ?_); exact continuous_iff_continuousAt.mpr fun i=> (Reader.fresh_smooth Q _ _ _ (own Z r u) (h0 i _ (Nat.le_of_lt_succ j.isLt))).continuousAt.comp (f:=fun i:I=>(g' i, o i)) (( (continuous_pi (f:=g') fun j=> by unfold g' position; fun_prop ).prodMk co).continuousAt)
omit cx cy
/-- one genuine joint-test witness in center,x,y coordinates, uses no T-density displacement.
Point or Finite complex signed at any shape. Each terms is measured. Variations retained.
E.g. for the M.4 inverse query can also call this on the Center/nail supports. -/
def Twice {X:Type}[MeasurableSpace X] (μ:VectorMeasure X ℂ)(Y D D': X→ℂ)(q:ℝ) :=
    μ.Integrable Y ∧ μ.Integrable D ∧ μ.Integrable D' ∧
    ‖μ.integral Y (ContinuousLinearMap.mul ℝ ℂ) - μ.integral D (ContinuousLinearMap.mul ℝ ℂ)‖ ≤ q*μ.variation.real univ ∧
    ‖μ.integral Y (ContinuousLinearMap.mul ℝ ℂ) - μ.integral D' (ContinuousLinearMap.mul ℝ ℂ)‖ ≤ q*μ.variation.real univ
private lemma inside {X:Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] {Y D' D'': X→ℂ} (μ:VectorMeasure X ℂ)[IsFiniteMeasure μ.variation] {q:ℝ}
    (y : Continuous Y) (d:Continuous D')(w:Continuous D'') (h:∀ i, ‖Y i-D' i‖ ≤ q)(H:∀ i, ‖Y i-D'' i‖ ≤ q) : Twice μ Y D' D'' q := by
  have Y' : μ.Integrable Y := y.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have F : μ.Integrable D' := d.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have V : μ.Integrable D'' := w.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h (A':X→ℂ) (v:μ.Integrable A') (h:∀ i, ‖Y i-A' i‖ ≤ q) : ‖μ.integral Y (ContinuousLinearMap.mul ℝ ℂ)-μ.integral A' (ContinuousLinearMap.mul ℝ ℂ)‖ ≤ q*μ.variation.real univ := by
    rw [ ← VectorMeasure.integral_sub Y' v ]; exact (VectorMeasure.norm_integral_le_of_norm_le_const (Eventually.of_forall h)).trans_eq
      (by rw [ContinuousLinearMap.opNorm_mul, mul_one])
  exact ⟨Y',F,V,h D' F (by assumption),h D'' V H⟩

include H hA h'A hB hW h'B hw hQ hZ hδ hF hM
variable (S0': StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
lemma twice (hd:∀ i,d i ≤ z)(he:∀ j,e j≤z)(hh:h≤z) (hL:0≤L) (hn:0<n)
    (paid : Calibrated G t) (S0': StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
    (η:ℝ)(hη:0<η)(dη:η<1)(P:ℕ): ∀ᶠ b:ℝ in atTop, ∀ᶠ p:ℕ in atTop, ∀ a c:ℝ, 0<c→ c≤a →
    Round Vx t S0 hd he p a b W A B → Round Vx t S1 (fun _=>hh) he p a b W {0} B →
    ∃ C :ℝ, 0<C ∧ ∀ᶠ r in late, ∀ T ≥ W, c*g r^(-b) ≤ T → T ≤ a*g r^(-b) →
      ∀ E:Set E4, IsCompact E → ∀ u∈Balls L G d, ∀ v∈Balls L G e, ∀ q:Viewers F, ∀ μ:VectorMeasure (↥E × ↥A × ↥B) ℂ, IsFiniteMeasure μ.variation →
        let o (i:↥E × ↥A × ↥B) := ((q,i.1.val) : Owner F)
        let Y i:=total F Z d e (o i) r T i.2.1.val i.2.2.val u v; let X i:= centerD F Z h e (o i) r T i.2.2.val v
        let c' i:=purchased Vx u i.2.1.val h p (t r); let c'' i:= coefficients F Z Q d h (o i) r i.2.1.val u
        Twice μ Y (fun i=>X i (c' i)) (fun i=>X i (c'' i)) (C*T ^(-((h:ℝ)+η))*(g0 G r)^P) := by
  have H' := listing F Z Q H hZ hQ hA h'A hB h'B hW hw hM hδ hF hd he hh S0' hL paid P η hη dη hn
  filter_upwards [H'] with b L'; refine L'.2.mono fun p X a c hp ha H0 V=>?_
  obtain ⟨C,hC,E⟩:= X a c hp ha H0 V; have L:= guest F Q (h:=h) hQ hM hδ hF
  refine ⟨C,hC,?_⟩; filter_upwards [ L,E,self_mem_nhdsWithin] with r L E hr T ht k f Q' hc' u hu v hv q μ h' o Y S' cX cW
  let J:= ↥Q' × ↥A × ↥B; let x:J→Points n:=fun i=>i.2.1.val; let y:J→Points m:=fun i=>i.2.2.val; let o':J→E4:= fun i=>i.1.val
  haveI := isCompact_iff_compactSpace.mp hc'; haveI:= isCompact_iff_compactSpace.mp hA; haveI := isCompact_iff_compactSpace.mp hB
  have h1:Continuous x := by unfold x J; fun_prop
  have h2:Continuous y := by unfold y J; fun_prop
  have h3 : Continuous o' := by unfold o' J; fun_prop
  have i(i:J): x i∈A:=i.2.1.property
  have j(i:J): y i∈B:=i.2.2.property
  have U':= affection F Z hδ hF x y o' h1 h2 h3 i j hr ht u v q
  have A'(α : J→Sec G h)(ha:∀ i,Continuous (fun j=>coord i (α j))) : Continuous (fun i=>S' i (α i)) := address F Z h'B hW y o' h2 h3 j hr ht v q ha
  have P (y y':ℂ)(t u:Sec G h→ₗ[ℂ]ℂ)(c c':Sec G h)(B:ℝ)(h:checkPrice y y' t u c c' ≤ B) : ‖y-t c‖ ≤ B ∧ ‖y-t c'‖ ≤ B := by
    unfold checkPrice at h; have q:=opPos (t-u); constructor <;> linarith [norm_nonneg (y-y'),norm_nonneg (y-t c),norm_nonneg (y-t c'),norm_nonneg (y-y'-(t-u) c')]
  refine inside μ ?_ (A' _ (pave H h'A x h1 i u p)) (A' _ (actual_cw F Z Q x o' h1 h3 u q (h0:=fun i' k hh=> L _ (i i') _ (j i') _ k hh)))
    (fun v' =>(P _ _ _ _ _ _ _ (E T ht k f _ (i v') _ (j v') (o v') u hu v hv)).2) (fun v'=> (P _ _ _ _ _ _ _ (E T ht k f _ (i v') _ (j v') (o v') _ hu _ hv)).1)
  exact U'
end YM.FVA2.GradedFar259.Original

