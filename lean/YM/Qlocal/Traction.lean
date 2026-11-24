import YM.Qlocal.Actual
/-!
# Operational marked supplier, ROUGH qlocal on chosen real data.

 Component towards full proof. This stage pays for repeated exact propagation
 of signed data on the dressed Run representation carrying *their own smallness*,
 in the FULL marker algebra and all field directions.Finances the strong K
 and repeated affordable norm. It is *not* an assertion that its canonical
 curvature/test models or differences from Fk meet that price yet, nor that
 the only regular propagating discrepancy is charged forever at a cup ratio:
 when no cumulative subpower claim available on a long stretch, the literal
 priced-radii histories with monotone calculated shrinking are used here,
 NOT at physical reporting radii. True post projection to that last norm is
 an additional cost in Ph.K.Window. Also note exact operations here on ANY
 Ω include Ω = IndependentTests. NOT claiming the outputs ℂ multilinear
 yet (see next version). No rank cap or bound on the number of slots for the
 first conclusion, `restore` on fixed finite allowed degree and Close only.

 This does propagate *any* launched marked data satisfying that Peak, on
 that same trajectory, doesn't build the input packets in this theorem. Covers
 the real component `required result` 3 (after one or a sequence of the indicated
 genuine reclosure choices, not after *any* further analytic approximation mask/layout
 changes), with relative weights in continuing and any fixed load. Along with
 Restore/Continued. Immediate direct suppliers `Leasing/Fortune`, `Titan/...`
 use the actual registration/coupling with all markers mixed. Local reclosure of
 the analytic Marked Fk prescription (incl MARK mask, profile & state choices
 and real estimates relative to old vacuum.E) and propagated small tails from that
 prescription remains separate obligation. Likewise curvature packets initialization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Actual
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Frigus Time Coat
open Program Program.Camp Program.Certificate
variable {Ω V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge} {m k p N j k' z n l v : ℕ} {δ r θ u E C ℓ: ℝ}
section deliver
variable (X:Run G) (η:ℕ→ℝ)(H T:ℕ→ℕ)(Q:Camp X.kit η H T)
set_option quotPrecheck false
local notation "a"=> X.alloy.B.a
local notation "F"=> X.kit
local notation "C₀"=> X.family
local notation "β"=> X.family.path.β N p
local notation "e"=> Coat.gStep (β (m+1))
variable (Y : (m:ℕ)→ RG.Rep G (X.alloy.B.a.S.side m p))
    (P:ℕ→Floe.Layout G) (Γ:ℕ→ Floe.Pace.Coin)
    (h : JourneyK X.alloy X.kit X.T P Γ z N p k Y)
variable (u:V→ℝ)(c:B.Mode→ℝ){o:(m:ℕ)→ V→Site (X.alloy.B.a.S.side m p)}{s:(m:ℕ)→ V→Support (X.alloy.B.a.S.side m p)}
    (j:ℕ) (U:Taste Ω (o j) (Y j) B)
    [Fintype V] [Nonempty V] [Nonempty Ω]
    (hC:Spirit c) (hu:∀ i,0 < u i)
    (Z:(m:ℕ)→Taste Ω (o m) (Y m) B)(M:Protocol X.alloy.B.a p Ω B Y o)
    (hS:Agenda (A:=X.alloy) o s z j) (hv:j ≤ N)(hr:z ≤ j)
local notation "C★"=> rent u c
local notation "V★"=> Hull.soft
local notation "uZ"=> Hull.divisor (a)
structure Through (l v:ℕ)(ε:ℝ): Prop where
 drive : Q.Trip o s u c j U M Z z
 point : ∀ i,z ≤ i→ i ≤ j→ HasSlots (Y i).p (Y i).activities ∧ (X.family.path.β N p i)∈ band a i ∧ (Y i).beta=X.family.path.β N p i ∧
          ∀ x Vw, (((Z i).leaf x).density Vw).part B.quiet=((X.family.path.rep N p i).eval Vw:ℂ)
 lane : ∀ i:ℕ,∀ (h':z ≤ i)(hk':i<j), ExactStep (X:=Ω) (pins X Y P Γ h (i+1) (h'.trans (Nat.le_succ _)) (hk'.trans_le hv)) (pins X Y P Γ h i h' (hk'.le.trans hv)) (o (i+1)) (o i) (Z (i+1)) (Z i)
 warm : Hull.Close (a) z j → Certificate.Rank l B→ ∀ i,z ≤ i→ i < j →
      let g:= X.family.path.β N p (i+1); let ε₁:= V★ ε g; let κ:=forcedDivisor X.family i
      let b:= Hull.hard (a) i; let w := Coat.gStep g ^ v
      Peak (Y i) (o i) (Z i) C★ (Y i).p.supportExponent ε₁ (b * w) ∧ Nonempty (RelativeBudget (a|>.budget i) (Z i) u κ c ((Real.exp 1+1)*ε₁) (κ*w))
-- combines structural clocks for any. (later compare sharper Fk using further lemmas)
include Q h hC hu hS
variable (t:ℝ) (l v : ℕ)
lemma arranged (hr':Trip Q o s u c j U M Z z) (hQ: ∀ i≥z, ShowT F η H T Q i l v t): Through X η H T Q Y P Γ h u c (s:=s) j U Z M hv l v t:=
    ⟨hr', fun i he hτ=> by obtain ⟨h₁,h₂,-,h₃,hq,hF⟩:= continued X Y P Γ h Q j u c U hC hu Z M hr' hS hv he hτ; exact ⟨h₁,h₂,h₃,hq⟩, fun i he ht=> (continued X Y P Γ h Q j u c U hC hu Z M hr' hS hv he ht.le).2.2.2.2.2 ht,fun hr hk i ht he=> restore X Y P Γ h Q j u c U hC hu Z M hr' hv (hQ i ht) he ht hk hr ⟩
-- creation of program.RO.
omit h hC hu hS
abbrev Transports (l t:ℕ) (r:ℝ): Prop:= ∀ (j:ℕ) (hk:z ≤ j) (hi:j≤N), ∀ (V Ω: Type) [Fintype V] [DecidableEq V][Nonempty V][Nonempty Ω]
     (B:Marker.Census V)(u:V→ℝ)(c:B.Mode→ℝ)(o:(m:ℕ)→ V→Site (X.alloy.B.a.S.side m p))(s:(m:ℕ)→ V→Support (X.alloy.B.a.S.side m p))(U:Taste Ω (o j) (Y j) B), Spirit c→ (∀ i,0 < u i) → Agenda (A:=X.alloy) o s z j→ Peak (Y j) (o j) U (rent u c) (Y j).p.supportExponent 1 1 → (∃ d, RetainsDeclared d U (s j))→ ∃ Z, Through X η H T Q Y P Γ h u c (s:=s) j U Z (fun _ _=> True) hi l t r
include Q h
lemma bearable (hQ:∀ i≥z, ShowT F η H T Q i l v t) : Transports X η H T Q Y P Γ h l v t:= by
 intro i hi he V Ω hx₁ hx₂ hx₃ hx₄ B u c o s K hC hv hT ht hh; obtain ⟨Z,hZ⟩:= Q.realistic h o s u c i hC hv K hT ht hh he hi; exact ⟨Z, arranged X η H T Q Y P Γ h u c i K hC hv Z _ hT he t l v hZ hQ⟩ -- explicit binder names.X.Inf.
-- final application. Boss.Amountance.Heter.O posterior.Need also anytime near.
omit h
lemma trajectory (h0:Appointment X η H T Q) (k:ℕ) (hb:0<t) : ∃ (R:Floe.Step.PlanV.Roots (G:=G) X.metals.p.profile X.metals.K X.metals.p.kernel) (G' : R.Tab X.rolls), TicketP X.alloy X.kit R G' ∧ ∀ᶠ z in atTop,∀ N≥ z, ∃ (P:ℕ→ Floe.Layout G)(Γ:ℕ→Floe.Pace.Coin), Floe.Step.PlanV.Path R X.alloy G' (Burn.horizon k) N z P Γ ∧∀ p:ℕ,∃ Y:∀ m,RG.Rep G (X.alloy.B.a.S.side m p),∃ hX:JourneyK X.alloy X.kit X.T P Γ z N p k Y,Transports X η H T Q Y P Γ hX l v t:=by
 obtain ⟨R,G',h,hE⟩:= tickets X η H T Q h0 k l v t hb
 refine ⟨R,G',h,hE.mono (fun z ht N hN =>?_)⟩; obtain ⟨h,P,Γ,hV,hL⟩:= ht N hN
 refine ⟨P,Γ,hV,fun p=>?_⟩; obtain ⟨Y,hB⟩:= hL p; exact ⟨Y,hB,bearable X η H T Q Y P Γ hB t l v h⟩
end deliver
end YM.Qlocal.Actual
