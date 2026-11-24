import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Thermostat
/-! # Complete the compact G.1 estimate relative to the BB upstream purchases
    with actual fields at both homes. Round and Horizon not needed to bootstrap!
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d}
    (hJ:Leading U J) (P:Realized J Y N A (Paper.meter U J N.criterion)) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "FW" => Paper.point U J
local notation "ψ" => GroupS.ψ N.criterion M ν
local notation "Z" => GroupS.gaugeN N.scheme N.criterion M ν

variable (h : Shop U J N) (hp: normal U J N.store) {r T:I→ℝ}(hr:Tendsto r L late)(ht:∀ᶠ i in L,T i∈ Icc 1 2) (hQ:Mixture U J N d) (hψ: Mixture U J N 6)
local notation "η" => Quotes.post T
local notation "φ" => minute U J N ν M
local notation "RR" => (fun i:I=>r i*T i)
local notation "ρ" => (t∘r)
set_option quotPrecheck false
local notation "dE" i:max => (personal J Y (RR i) (r i) d).symm.toLinearMap
local notation "Q" => guardTrial N ν M
local notation "E" i:max => STrial J Y N t ν M d (r i) (T i)

lemma oppose (p : ℕ) (i : I) : columns (dE i) * columns ((E i) p) =
    columns (L' N ν M d (η i) p (ρ i)) := by
    rw [STrial, ← columns_mul, ← mul_assoc,
      show (dE i)*(personal J Y (r i*T i) (r i) d).toLinearMap=(1:FieldEnd G d) from LinearMap.ext (fun v=> (personal J Y (RR i) (r i) d).symm_apply_apply v),one_mul]; rfl

lemma expires (p:ℕ) {U V H:I→ ScaleCost.Operator G d} (h:Tendsto H L (𝓝 1)) (hv: Issue L Pose.home V) {w:I→ℝ}
    (he:∀ i,U i*H i=V i)(hx: Issue L w (fun i=> H i-1)): Issue L w (fun i=> U i - V i) := by
  have e : ContinuousAt Ring.inverse (1:ScaleCost.Operator G d).det := by rw [Ring.inverse_eq_inv',det_one]; exact continuousAt_inv₀ one_ne_zero
  have ht:Tendsto (fun i=>(H i)⁻¹) L (𝓝 1) := by simpa [Function.comp_def] using (continuousAt_matrix_inv _ e).tendsto.comp h
  have hp: Issue L Pose.home U := by
    refine (Issue.multiply hv (Issue.coverage ht)).congr' ?_ (EventuallyEq.refl ..)
    filter_upwards [(continuous_id.matrix_det.tendsto _ |>.comp h).eventually (eventually_ne_nhds (by simp : (1:ScaleCost.Operator G d).det≠0))] with i hi
    change stiffness ( V i * (H i)⁻¹ ) = _; change (H i).det ≠ 0 at hi; rw [ ← he,mul_assoc, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hi),mul_one ]; rfl
  apply matrixPay.mpr; intro a b
  apply (isBigO_neg_left.mpr (matrixPay.mp ((Issue.mult hp hx).congr_right (g₂:=w) (fun i=>one_mul _)) a b)).congr_left; intro i; rw [mul_sub,mul_one, he, Matrix.sub_apply, Matrix.sub_apply, neg_sub]
include hJ hp H P hr ht hQ h
lemma interchange (p:ℕ) : Notes L Pose.home ρ (δ ∘ r) p Pose.home (fun i=>dE i) (fun i=>Q (η i) d) := by
  let g i:=δ (r i)^(p+1); let X i:=columns ((E i) p); let payt:= Pose.guaranteed U J hJ N hp M H h
  have hf: Issue L g (fun i=>X i - 1) := by
    refine matrixPay.mpr fun i j=>?_; let h:= billed U J Y N hJ P ν M H h hp hr ht hQ p
    refine (insertCoord _ h i (theory j)).congr' ?_ (EventuallyEq.refl ..); filter_upwards [voted U J Y N t hJ P ν M H payt hr ht p (d:=d)] with k hi; rw [hi]; unfold X; change _ = _ - (1:Operator G d) _ _; rw [ ← one_matrix ]; rfl
  have H' := expires p (stand_lead U J Y N t hJ P ν M H payt hr ht hQ p) (rumor_charge J Y N t P ν M H payt hr ht p (d:=d)) (oppose U J Y N ν M p) hf
  intro i j
  exact Coin.covered (one_paid _) (rumor_note J Y N t P ν M H payt hr ht p i j) (Fare.bare ((matrixPay.mp H' i j).congr_right fun k=>(mul_one _).symm))
include hψ
lemma estimate (p:ℕ)(hz:1 ≤ p) : Notes L Pose.home ρ (δ ∘ r) p Pose.home
    (fun i=> via Y (r i) (RR i) d) (fun i=>conversion Z (η i) d) := by
  have payt:= Pose.guaranteed U J hJ N hp M H h; obtain ⟨hr',hd⟩ := later_G hr ht sim
  have h' :=peson _ _ _ _ H P payt hr; have hZ : ∀ᶠ i in L, |ρ i| ≤1 := hr.eventually ( (coupling_payment sim payt).mono fun i hi=>hi.2.1 )
  let κ i:= ψ (η i); have hh (i:I) : Program.Rooted (κ i) := ((H.dilation ν).check.led ..).start
  let W i:=stand (A d (t (RR i))); let ζ i:=stepV (κ i) (Scale.Measure.adjust N.scheme N.criterion d)
  have V:Notes L Pose.home ρ (δ ∘ r) p Pose.home W ζ := by
    intro i j; simp_rw [ζ, prose_subst _ _ (hh _)]
    exact Coin.substitute h' hZ (one_paid _) (hr'.eventually ( (coupling_payment sim payt).mono fun i hi=> hi.2.1 ))
      (clock_unit U J Y N hJ P ν M H h hp hr ht hψ p hz) hh (Coin.quick (one_paid _) (paper J Y t M H P payt hr' p i j) hd )
  intro i j; refine (Notes.product h' hZ (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) (one_paid L) (interchange U J Y N hJ P ν M H h hp hr ht hQ p) V i j).congr ?_ ?_ (Eventually.of_forall fun i=>one_mul (Pose.home i))
  · filter_upwards [hr'.eventually (P.relates d)] with i hi; apply congr_arg (fun f:FieldEnd G d=> columns f _ _); ext1 v
    change (frame Y (r i) d).symm (frame J (RR i) d (W i v))=(frame Y _ d).symm (frame Y (RR i) d v); exact congr_arg (frame Y (r i) d).symm (hi v).symm
  apply Eventually.of_forall; intro i; dsimp only; unfold guardTrial ζ κ
  rw [mul_assoc, ←Scale.Frame.step_mul _ _ _ (hh i),(base_adjust N M H).turn,Scale.Frame.step_one,mul_one]
end YM.FVA2.GradedFar259.Quotes
