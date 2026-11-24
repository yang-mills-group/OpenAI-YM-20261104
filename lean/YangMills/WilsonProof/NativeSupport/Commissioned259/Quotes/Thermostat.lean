import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Receipt
/-! # Real calibration of Scale ψ, via physical pair of the same contexts. Every aspect
of the log-test price needs the real calibration of this thermometer; hypothetical on upstream
purchases as stated. -/
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

variable (h : Shop U J N) (hp: normal U J N.store) {r T:I→ℝ}(hr:Tendsto r L late)(ht:∀ᶠ i in L,T i∈ Icc 1 2) (hQ:Mixture U J N 6)
local notation "η" => Quotes.post T
local notation "φ" => minute U J N ν M
local notation "RR" => (fun i:I=>r i*T i)
local notation "ρ" => (t∘r)
include hJ hp H h hr ht P
lemma rumor_unit (p:ℕ) : (fun i=> φ p (r i) (T i)) =O[L] (δ ∘ r) := by
  have H0:= Pose.guaranteed U J hJ N hp M H h
  have he := homebound (Tunes.excess (one_paid _) (hr.eventually ((coupling_payment sim H0).mono fun i hi=>hi.2.1)) (peson _ _ _ _ H P H0 hr) p 0 (Nat.zero_le _) (ratio_tune N ν M H ht))
  have hh (i:I) : crop 0 (t (r i)) (ψ (η i)) = 0 := by rw [crop_apply,Finset.sum_range_succ,Finset.sum_range_zero, zero_add, ((H.dilation ν).check.led _).start,mul_zero]
  simp_rw [Function.comp_def,hh,sub_zero] at he
  exact ((Complex.reCLM.isBigO_comp ..).trans he).congr_right (fun i=>by simp [Pose.home,Function.comp_apply])
include hQ
lemma thermostat (p:ℕ)(hz:1 ≤ p) : (fun i=> t (RR i) - φ p (r i) (T i))=O[L] (fun i=> (δ (r i))^(p+1)) := by
  let F := booth (tsupport (Rose.test N.criterion)) L; have he:Tendsto Prod.fst F L:= tendsto_fst
  let X (i:I) (x:Points 3) b := FW (RR i) 6 3 x (ret G b)
  let Y' (i:I):= φ p (r i) (T i); let g := fun i=>δ (r i)^(p+1)
  exact reread N M H Y' X (w:=g)
    (fun b=> after U J Y N hJ P ν M H h hp (hr.comp he) (he.eventually ht) hQ (Alcove.testing (Rose.test N.criterion)) Prod.snd placed p (ret G b))
    (isBigO_const_of_tendsto (((g0_zero sim).pow (p+1)).comp hr) one_ne_zero) (isBigO_refl g L)
    (rumor_unit U J Y N hJ P ν M H h hp hr ht p) ((pulse U J Y N hJ P ν M H h hp hr ht p).abs.eventually (ge_mem_nhds (by simp)))
    (((later_G hr ht sim).1.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))).mono fun i hi=>continuous_log3 (fun b=>Paper.smooth U J (ret G b) hi)) hz
lemma clock_unit (p:ℕ) (hz:1 ≤ p) : Coin L home ρ (δ∘r) p home (fun i=> (↑(t (RR i)):ℂ)) (fun i=> ψ (η i)) := by
  refine Coin.covered (one_paid _) (rumor_stamp N ν M H ht ρ p) (Fare.bare ?_); simp_rw [← Complex.ofReal_sub]; exact ((Complex.ofRealCLM.isBigO_comp ..).trans (thermostat U J Y N hJ P ν M H h hp hr ht hQ p hz)).congr_right fun i=> (mul_one _).symm
end YM.FVA2.GradedFar259.Quotes
