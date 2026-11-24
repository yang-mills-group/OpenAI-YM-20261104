import YM.Integration.FVA1Physical.Wilson.PacketOffer
import YM.MSbar.Ballet.Card

/-! A single weighted cutoff threshold for the actual mixed source, simultaneously in all admitted periods and exterior positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open YM.MSbar YM.MSbar.Mosaic YM.MSbar.Mosaic.Issue YM.Integration.FVA1Physical.Wilson
open YM.Integration.FVA1Physical.Round2.Curvature (clockReading)
open RGComparison.Core16 RGComparison.Core16.Spool

open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior YM.Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}

/-- The next measured conditional Haar step acts on an uncropped distributed
polynomial bank. The box and the signed bank may be chosen after the period. -/
def InheritedPort (A:Issue G) (χ:ChartRatio G) (J:Voice G) (p degree:ℕ) (y E:ℝ) (b:Site A.f)
    (Z:Positions (Primary A.c G)) : Prop :=
  ∀ (P:Palisade) (copied:Bool) (T:Nesting G A.f),BankPaid b y 0 p degree 0 T → (PowerSeries.coeff 0 T).totalDegree=0 →
    ∀ U∈A.regionX y b Z J P,|A.modelP y b Z P J
      (fun v=>clockReading p A.fClock T (chartLog A.fClock (packetConfig A J y b Z copied v))) U -
      taste p (innerColumn A χ J y (A.fClock•Z) b U (enterRows A T) p) A.fClock| ≤ E

private structure PacketPoint (G:Gauge) where
  scene : Issue G
  anchor : Site scene.f
  exterior : Positions (Primary scene.c G)

/-- Genuine stage pricing. The Gaussian, action, and source receipts are all
constructed before testing a period, source position, or admissible background. -/
theorem packet_receipt (χ:ChartRatio G) (J:Voice G) (H H':Stage) (K:Patch) (D:KernelChoices)
    (hG:G.Simple) (hD:K.Branches D G) (hQ:Clear G J) (hχ:LocalRatio χ)
    (M:StageCost) (i':G.ColorIndex) (p m degree:ℕ) (fits:degree ≤ (m+1)*(p+2))
    (f:ℝ→ℝ) (b θ:ℝ) (hr:p+2 ≤ m) (hm:4 ≤ m) (hf:Mosaic.Run atTop id f 0) (hθ:epsW p < θ) :
    ∀ᶠ x:ℝ in atTop, Ore M x K → ∀ A:Issue G, Issue.Paid A K H H' J x → A.S.kernel=D →
      Festival A χ p i' → ClockD A p m M.s x → Cs A χ M.s p m x i' (f x) b →
      Issue.Receipt A M x → ∀ (z:Site A.f) (W:Positions (Primary A.c G)), ‖W‖ ≤ hull x →
      InheritedPort A χ J p degree (tip G K.L x) ((tip G K.L x)^θ) z W := by
  let gate (x:ℝ) (v:PacketPoint G):Prop := Ore M x K ∧ Issue.Paid v.scene K H H' J x ∧
    v.scene.S.kernel=D ∧ Festival v.scene χ p i' ∧ ClockD v.scene p m M.s x ∧
    Cs v.scene χ M.s p m x i' (f x) b ∧ Issue.Receipt v.scene M x ∧ ‖v.exterior‖ ≤ hull x
  have core: ∀ᶠ x:ℝ in atTop,∀ v:PacketPoint G, gate x v →
      InheritedPort v.scene χ J p degree (tip G K.L x) ((tip G K.L x)^θ) v.anchor v.exterior := by
    apply Mosaic.cofi (S:=gate)
    intro X P hX h
    let A i:=(P i).scene
    let W i:=(P i).exterior
    let z i:=(P i).anchor
    let y i:=tip G K.L (X i)
    have rise:Tendsto y atTop atTop:=(Work.E09.betaF_growth G K.L).comp hX
    have hp:∀ᶠ i:ℕ in atTop,Issue.Paid (A i) K H H' J (X i):=Eventually.of_forall fun i=>(h i).2.1
    have hk:∀ᶠ i:ℕ in atTop,(A i).S.kernel=D:=Eventually.of_forall fun i=>(h i).2.2.1
    have hW:∀ᶠ i:ℕ in atTop,‖W i‖ ≤ hull (X i):=Eventually.of_forall fun i=>(h i).2.2.2.2.2.2.2
    let k:=m+1
    have th:=Mosaic.Issue.thorn_top rise (k*(p+2))
    have positive := (Mosaic.Issue.gate hX hG hX K.L (k*(p+2))).mono fun i he=>he.1.le
    obtain ⟨Q,τ,c,hτ,hc,grants⟩:=Mosaic.Issue.grants hX χ J H H' K D hG hD hQ hχ hp hk W hW z
      (show 3 ≤ k by dsimp [k]; omega) 0 0 positive th
    obtain ⟨a,_,cut⟩:=Lodge.top_hat k
    let w i:=vol (y i)
    let cover i:=Lodge.masking (w i) Lodge.sea
    have hw:Tendsto w atTop atTop:=(Alto.broad.comp rise).atTop_mul_const (r:=(32:ℝ)⁻¹) (by positivity)
    have hat:∀ᶠ i:ℕ in atTop,Lodge.Hat k (w i) (w i*a) (cover i):=
      (hw.eventually_ge_atTop 1).mono fun i hi=>Lodge.cool cut hi
    have staff:∀ᶠ i:ℕ in atTop,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i) ∧
        Cs (A i) χ M.s p m (X i) i' (f (X i)) b ∧ Issue.Receipt (A i) M (X i) :=
      Eventually.of_forall fun i=>⟨(h i).2.2.2.1,(h i).2.2.2.2.1,(h i).2.2.2.2.2.1,(h i).2.2.2.2.2.2.1⟩
    obtain ⟨E,rate,ok⟩:=offer_packets hX χ J H H' K D hG hQ hχ hp hk W hW M i' staff z
      (Eventually.of_forall fun i=>(h i).1) Q hr (hf.subclock hX) rfl (by omega)
      hm hτ hc grants cover hat degree fits
    filter_upwards [ok, rate θ hθ] with i good small
    intro _ copied T bank flat U inside
    exact (good copied T bank flat U inside).trans ((le_abs_self (E i)).trans small)
  filter_upwards [core] with x hx ore A paid kernel fest clock c receipt z W hW
  exact hx ⟨A,z,W⟩ ⟨ore,paid,kernel,fest,clock,c,receipt,hW⟩

end YM.Integration.FVA1Physical.Wilson

