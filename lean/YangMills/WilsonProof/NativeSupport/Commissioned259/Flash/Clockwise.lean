import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Rise
/-! # Spending the aperture cost. Both logs conventions.
  Moment/phase & shape derivatives earned by those lemmas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ} {I:Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {x:I→Points n}{y:I→Points m}{r T:I→ℝ} (R:Room W c δ A B) {E:Type*} [Norm E]
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge} {N : WilsonPrescription G} (ν:ℝ) {sim : G.Simple} {C : Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S) (Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (H0: LogTrace U Q.port)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ: MS.Land.Prescription (Press.portDeck G)} {dial:Bool}
    (H:Main.Match N sim M σ dial) {A0:∀d:ℕ,ℝ→Change G d}(P:Realized J Y N A0 (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)(hJ: Leading U J)(hp: normal U J N.store)
    (h:Aim F G W a b r T)(hb:0<b) (hx:∀ᶠ i in F,x i∈A)(hy:∀ᶠ i in F,y i∈B)
local notation "t" => Paper.meter U J N.criterion
local notation "g" => (fun i=>g0 G (r i))
local notation "Jx" => (fun i:I=> joins (x i) (y i) (T i))
variable {p:I→E} {w:I→ℝ}
include R h sim
lemma taper : T =O[F] (fun i=> g i ^ (-b)) := by
  refine IsBigO.of_bound a ?_
  filter_upwards [h.bud,aspirant R h,h.reach.eventually (g0_pos sim)] with i v l j; rw [Real.norm_of_nonneg (zero_le_one.trans l), Real.norm_of_nonneg (by positivity)]; exact v
lemma today (u:ℝ) : (fun i=>r i*T i)=O[F] (fun i=>g i^u) := (((length sim (u+b)).comp_tendsto h.reach).mul (taper (sim:=sim) R h)).congr' (EventuallyEq.refl ..) ( (h.reach.eventually (g0_pos sim)).mono fun i hi=> by dsimp only [Function.comp_apply]; rw [ ← Real.rpow_add hi, add_neg_cancel_right ] )
lemma clocks (n:ℕ) : (fun i=> OPE.Log.badge (r i)^n)=O[F] (fun i=> ((g i)⁻¹)^(2*n)) := by
  have hr:=h.reach; have H : (fun i=> OPE.Log.badge (r i))=O[F] (fun i=> ((g i)⁻¹)^2) := by
    apply IsBigO.of_bound (2*G.slopeConstant⁻¹); filter_upwards [hr.eventually (adjustment sim),hr.eventually (holds_cash.eventually_ge_atTop 1), log_pays hr,h.reach.eventually (g0_pos sim)] with i eq w h p; rw [ Real.norm_of_nonneg (zero_le_one.trans h), Real.norm_of_nonneg (by positivity) ]; rw [OPE.Log.badge,OPE.run,← Real.log_inv]; change 1+ cash (r i) ≤ _; rw [eq] at *; linarith
  exact (H.pow n).congr_right (fun i=> by rw [pow_mul])
lemma now_pays (H:Allowance F r w p) : ∃ k:ℕ, p=O[F] (fun i=> ((g i)⁻¹)^k * w i) := by
  obtain ⟨k,V⟩:= H; exact ⟨2*k,( V.trans ((isBigO_refl w F).mul (clocks R h k (sim:=sim)))).congr_right (fun i=>mul_comm ..) ⟩
lemma cheap (H:Allowance F r (fun i=> r i*T i) p) (d:ℕ) : p=O[F] (fun i=> g i^d) := by
  obtain ⟨k,V⟩:= now_pays R h (sim:=sim) H
  refine (V.trans ((isBigO_refl _ _).mul (today (sim:=sim) R h (d+k:ℕ)))).congr' (EventuallyEq.refl ..) ?_
  filter_upwards [h.reach.eventually (g0_pos sim)] with i h; rw [ Real.rpow_natCast,add_comm d k,pow_add, inv_pow, ←mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt h)),one_mul]
include hb
lemma cents (H:Fare T F w p) : p=O[F] (fun i=> w i*(g i)⁻¹) := by
  obtain ⟨n,H⟩:=H; apply H.trans ((isBigO_refl w F).mul ?_); simpa only [Real.rpow_neg_one, Function.comp_apply] using (ScaleCost.log_any hb ((pace sim).comp h.reach) (aspirant R h) (taper R h (sim:=sim)) n (1:ℝ) zero_lt_one)
include U J Y ν H S0 S1 hJ H0 P hp hx hy
lemma decamps (v w:I→ Viewers U)(u:Tags G d (n+m)) (p:ℕ):
    (fun i=> physicalY U Y (v i) u (r i) (Jx i)-physicalY U Y (w i) u (r i) (Jx i))=O[F] fun i=> g i^p :=
  cheap (sim:=sim) R h (onRows R ν U Y Q H0 (taking U J Y N hJ P M H S1 hp) H
    (G1_step U J Y N hJ P ν M H S1 hp S0) (Pose.guaranteed U J hJ N hp M H S1) h hb hx hy u v w).2 p
end YM.FVA2.GradedFar259.Flash
