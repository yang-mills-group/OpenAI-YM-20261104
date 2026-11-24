import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Realized
/-! # Implication: W compact prices from (C5) carry over to this actual H
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original
open scoped Topology ContDiff Classical BigOperators
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G)
    {A : ∀ d:ℕ, ℝ→Change G d} (hJ : Leading U J) (s : Shop U J N) (hp : normal U J N.store)
    (P : Realized J Y N A (Paper.meter U J N.criterion))
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "FW" => Paper.point U J
local notation "τ" => Paper.meter U J N.criterion
local notation "X" => Scale.Measure.start N.scheme N.criterion
local notation "Q" => Scale.Measure.adjust N.scheme N.criterion
local notation "FX" => Paper.point U Y
local notation "K" => Scale.Measure.outlook N.scheme N.criterion

variable {r:I→ℝ} (hr:Tendsto r L late)
include hJ hp H hr s
lemma pupil (R:Alcove)(x : I→Points R.n) (hx : ∀ᶠ i in L,x i∈ R.K) (d p:ℕ) : Eval L home (τ ∘ r) (δ ∘ r) p home (fun i=>FW (r i) d R.n (x i)) (fun i=> fxt (X d) (x i)) := by
  intro u; refine ⟨compact_tunes _ (orders N M H).light R.cost R.space hx _, Fare.bare ?_⟩
  have he:= F4 U J hJ N hp M H s R (word u) p; simp_rw [array_eq] at he
  have ht : Tendsto (fun i=> (r i,x i)) L (booth R.K late) := hr.prodMk (tendsto_principal.mpr hx)
  exact (he.comp_tendsto ht).congr_right fun i=>(mul_one _).symm
include P
lemma cut (R:Alcove)(x : I→Points R.n)(hx : ∀ᶠ i in L,x i∈ R.K) (d p:ℕ) : Eval L home (τ ∘ r) (δ ∘ r) p home (fun i=>FX (r i) d R.n (x i)) (fun i=> fxt (K d) (x i)) := by
  intro u
  have h := Pose.guaranteed U J hJ N hp M H s
  let P' i := stand (A d (τ (r i))); let Q' i:= FW (r i) d R.n (x i)
  have he := labels (peson _ _ _ _ H P h hr) (hr.eventually ((coupling_payment sim h).mono fun i hi=>hi.2.1))
    (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) (Eventually.of_forall fun i=> le_rfl (a:=home i)) Q' (fun i=>fxt (X d) (x i)) (pupil U J N hJ s hp M H hr R x hx d p) (paper _ _ _ _ H P h hr p (d:=d)) u
  refine he.congr ?_ (Eventually.of_forall fun i=>?_ ) (Eventually.of_forall fun i=>by unfold Pose.home; simp)
  · filter_upwards [hr.eventually (P.relates d)] with i hi;  change ( ( FW (r i) d R.n (x i) ).compLinearMap (fun _=>stand (A d ((τ∘r) i))) ) _ = FX (r i) d R.n (x i) (word u); rw [MultilinearMap.compLinearMap_apply,Paper.use,Paper.use]; unfold Original.own; simp_rw [hi]; rfl
  unfold Scale.Measure.outlook; simp [fxt_m]
end YM.FVA2.GradedFar259.Quotes
