import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Stands
/-! # QScale comparison at the ACTUAL trial, simultaneous on compact ratio,
then real-coordinate error price via the Prepared SetEq on W
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
local notation "LX" => guardTrial N ν M
local notation "FX" => Paper.point U Y
local notation "FW" => Paper.point U J
local notation "ψ" => GroupS.ψ N.criterion M ν
local notation "V" => Scale.Measure.start N.scheme N.criterion
local notation "VK" => Scale.Measure.outlook N.scheme N.criterion

variable (h : Shop U J N) (hp: normal U J N.store) {r T:I→ℝ}(hr:Tendsto r L late)(ht:∀ᶠ i in L,T i∈ Icc 1 2) (hQ: Mixture U J N d)
local notation "η" => Quotes.post T
local notation "RR" => (fun i:I=>r i*T i)
local notation "ρ" => (t∘r)
abbrev Λ (d:ℕ) (p:ℕ) (r T:ℝ) := stand (invoice J Y N t ν M d r T p)
abbrev ordinary (d p:ℕ) (r T:ℝ) (x:Points n) : Structure1.Point G d n:= (FW (r*T) d n x).compLinearMap (fun _=> Λ U J Y N ν M d p r T)
abbrev minute (p:ℕ) (r T:ℝ) : ℝ:= rumor N ν M (-Real.log T) (t r) p
local notation "φ" i:max "," p:max => minute U J N ν M p (r i) (T i)
include H h hp hJ hr ht P
lemma trial_eq (R:Alcove)(x:I→Points R.n)(hx:∀ᶠ i in L,x i∈R.K)(p d:ℕ) : ∀ᶠ i in L, ordinary U J Y N ν M d p (r i) (T i) (x i) =
    (FX (r i) d R.n (Real.exp (-(η i)) • x i)).compLinearMap (fun _=> L' N ν M d (η i) p (ρ i)) := by
  have payt:= Pose.guaranteed U J hJ N hp M H h
  filter_upwards [ht,voted U J Y N t hJ P ν M H payt hr ht p (d:=d)] with i ⟨h,k⟩ hi
  ext1 u; unfold ordinary Λ
  rw [hi,MultilinearMap.compLinearMap_apply,MultilinearMap.compLinearMap_apply, Paper.use,Paper.use]
  unfold Quotes.post; rw [neg_neg,Real.exp_log (by linarith),← mul_smul]; congr 1; funext j; exact (frame J (r i*T i) d).apply_symm_apply (frame Y (r i) d _)
lemma trial_coupled (R:Alcove)(x:I→Points R.n)(hx:∀ᶠ i in L,x i∈R.K)(p d:ℕ) :
    Eval L home ρ (δ∘r) p home (fun i=>ordinary U J Y N ν M d p (r i) (T i) (x i))
      (fun i=>fxt (couple (ψ (η i)) (V d)) (x i)) := by
  let Y₁ (i:I):= Real.exp (-(η i)) • x i; let Ω (i:ℝ×Points R.n) := i.1 • i.2; have hh: Continuous Ω :=by unfold Ω; fun_prop
  let Q:= Icc (1:ℝ) 2 ×ˢ R.K; let Z := Ω '' Q; have hZ : Z⊆ conf R.n :=by
    rintro i ⟨j,a,rfl⟩; exact Work.A05.smul_conf (zero_lt_one.trans_le a.1.1) (R.space a.2)
  let R' : Alcove := ⟨R.n,Z,(isCompact_Icc.prod R.cost).image hh,hZ⟩
  have hK : ∀ᶠ i in L,Y₁ i ∈ Z := by
    filter_upwards [hx,ht] with i he ⟨hi,h'⟩; unfold Y₁ Quotes.post; rw [neg_neg,Real.exp_log (by linarith)]
    exact ⟨(T i,x i),⟨⟨hi,h'⟩,he⟩,rfl⟩
  have payt:= Pose.guaranteed U J hJ N hp M H h
  let K i:= FX (r i) d R.n (Y₁ i); intro u
  have z := labels (peson _ _ _ M H P payt hr) (hr.eventually ((coupling_payment sim payt).mono fun i hi=>hi.2.1))
    (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) (one_paid _) K (fun i=> fxt (VK d) (Y₁ i))
    (cut U J Y N hJ h hp P M H hr R' Y₁ hK d p) (rumor_note J Y N t P ν M H payt hr ht p) u
  refine z.congr ?_ ?_ (Eventually.of_forall fun i=>by unfold Pose.home; simp)
  · exact (trial_eq U J Y N hJ P ν M H h hp hr ht R x hx p d).mono fun i hi=> (congr_arg (fun q:Structure1.Point G d R.n=>q (word u)) hi).symm
  filter_upwards [hx] with i hi
  change Reg.Point.story (status _ _) _= Reg.Point.story (fxt _ _) (word u); rw [fxt_c,moves _ _ ((H.dilation ν).check.led ..).start]
  exact scale_identity N ν M H _ (R.space hi) _
lemma true_charge : Tendsto ρ L (𝓝 0) := (heading J Y t M H P (Pose.guaranteed U J hJ N hp M H h) hr).mono_right nhdsWithin_le_nhds
lemma pulse (p:ℕ) : Tendsto (fun i=>φ i,p) L (𝓝 0) := trend N ν M H ht (true_charge U J Y N hJ P M H h hp hr ht) p
lemma attempt (R:Alcove)(x:I→Points R.n)(hx:∀ᶠ i in L,x i∈R.K)(p:ℕ)(u:Tags G d R.n) :
    (fun i=> ordinary U J Y N ν M d p (r i) (T i) (x i) u-array (V d) (x i) p (φ i,p) u)=O[L] fun i=>δ (r i)^(p+1) := by
  have payt:= Pose.guaranteed U J hJ N hp M H h
  let B i:= Reg.Point.story (fxt (V d) (x i)) u
  let C (i:I):= crop p (ρ i) ((B i).subst (ψ (η i)))
  let τ i := Pose.array (V d) (x i) p (φ i,p) u
  let F i:= ordinary U J Y N ν M d p (r i) (T i) (x i) u; let g i := δ (r i)^(p+1)
  have hf:= peson _ _ _ _ H P payt hr; have hh : ∀ᶠ i in L, |t (r i)| ≤ 1 := hr.eventually ((coupling_payment sim payt).mono fun i hi=>hi.2.1)
  let T':= one_paid L
  have hu:(F - C)=O[L] g := by
    have h := homebound ((Eval.fixed hf hh (hr.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) T' _ _ u (trial_coupled U J Y N hJ P ν M H h hp hr ht R x hx p d)).expense)
    simp_rw [fxt_c, moves _ _ ((H.dilation ν).check.led _).start] at h
    exact h.congr_right fun i=> mul_one _
  have hp' : (fun i=>τ i-C i)=O[L] g := by
    simp_rw [τ,array_eq]
    exact (homebound (ScaleCost.clock_inserting T' hh hf (ratio_tune N ν M H ht) (compact_tunes _ (orders N M H).light R.cost R.space hx u)
      (fun i=> ((H.dilation ν).check.led _).start) p ((pulse U J Y N hJ P ν M H h hp hr ht p).abs.eventually (ge_mem_nhds (by simp)))
      ((rumor_stamp N ν M H ht (g:= δ ∘ r) ρ p).expense |>.extend (Eventually.of_forall fun i=>mul_one _)) )).congr_right fun i=> mul_one _
  exact (hu.sub hp').congr_left fun i=> by change F i-C i - (τ i-C i)=F i-τ i; abel
end YM.FVA2.GradedFar259.Quotes
