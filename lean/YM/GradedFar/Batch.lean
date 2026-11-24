import YM.GradedFar.OperatorPoly
import YM.GradedFar.Duplex
import YM.GradedFar.Attend
import YM.GradedFar.Wave
/-!
# Point/readout version of the comparison sales on SAME pose data

Plus `Attend.responds` supplying test bounds. Hypotheses on predecessor W still *required* in all
claims. They suffice by valuation proofs (Tariff), calendar telescoping (Stair), calibration
opening around both the field and clock (Render), physical recession of the real packet and its
phase comparison (Horizon), and the grid & precision extension (Earn). Thus not asking
already-interleaved G9,G1 or assuming that the receding geometry statements in the mathematical
text have been paid.

Exercise with P argument the *actual* H tower from the SAME F election. Next exported theorem derives
those inputs on it: `Prepared` (linkage & accumulation & centering) separately from `PoseFit`,
whose upstream physical control/clock inputs are hypotheses. Uses all n,h costs, include zero.
(The finite-arity/horizon set needed for each individual comparison determined in supplier lemmas.)
`PoseFit` here is not a Lean proof of the prior physical supplies; requires the piece exactly as stated.
Not a claim that `Main.Match` implies ANY of the physical inputs or graph integral IDs. Compare with
through-exterior kernel identities at appropriate calibration.

-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace Batch
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Neighbor
open YM.Integration.GradedFar.Tariff
open YM.Integration.GradedFar.Tariff.Playbill
open YM.Integration.GradedFar.Tariff.Crosser
open YM.Integration.GradedFar.Tariff.Billboard
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    (t:ℝ→ℝ)
local notation "g∴"=> strength G
structure Pose : Prop where
    running : Coupling G t -- derived separately from prior (F.3) hypothesis
    fixed n h: fixedPose F J Z t h n
    joint h: JointTicket F J Z h
    positions {m n} h (K:Set (Points n))(N:Set (Points m)){U B:ℝ} : 0 < U → 0 < B → IsCompact K → K ⊆ conf n →
        IsCompact N → N ⊆ Outside m → ∀ p:ℕ, GridPose F J Z t K N h U B p
structure Prepared : Prop where
    accrue : ∀ h,widens J P Z h t
    centering h: ∀ᶠ r in trail, Axil F P r h
    connects: Billboard.Connected F P

variable {t} (Ht: Pose F J Z t) (Zp:Prepared F J P Z t)
variable {n m d h p:ℕ} {e:Fin n→ℕ}{l:Fin m→ℕ}
local notation "A" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "W" => GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν
include H Ht Zp
lemma YPose : ClassExpansion F P A t n h:= stationary F J P Z M H _ Ht.running (Zp.accrue h) (Ht.fixed n h)
lemma budgets : Billboard.Held P h:= ⟨jump_steady J P Z M H h t Ht.running (Zp.accrue h) (SteadyUp.all J h
      ((makes F J Z M H h (Ht.joint h)).bootstrap F J Z M H h)), allot F P (Zp.connects h) (Zp.centering h)⟩
lemma coupons (H0:1≤p): Stamp P Z M ν t h p ∧ DialStamp Z M ν t p:=
    ⟨charged F P Z M ν H h p t H0 Ht.running (budgets F J P Z M H Ht Zp) (budgets F J P Z M H Ht Zp) (fun _=>YPose F J P Z M H Ht Zp) (fun _=>YPose F J P Z M H Ht Zp),
     award F P Z M ν H h p t H0 Ht.running (budgets F J P Z M H Ht Zp) (budgets F J P Z M H Ht Zp) (fun _=>YPose F J P Z M H Ht Zp) (fun _=>YPose F J P Z M H Ht Zp)⟩

lemma G1 {U B:ℝ}(hU:0<U)(hB:0<B) : G1Wide P Z M ν h t U B:=
    extension P Z M ν h H Ht.running (fun _ hi=>(coupons F J P Z M H ν Ht Zp hi).1) (fun _ hi=>(coupons F J P Z M H ν (h:=h) Ht Zp hi).2) hU hB
include ν in
lemma Q2 : Fork.Coat F R P h := Z_estimate F P R Z M ν H (Zp.connects h) (t:=t) ((coupons F J P Z M H ν Ht Zp (p:=1) le_rfl).1)
variable (Hq:LogTrace F R.port) {K:Set (Points n)}{N:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N⊆Outside m)
include Hq hK hx hN hz
include ν in
theorem booth : ∃ D:ℝ,0≤D ∧ ∀ U B:ℝ,G6 F R P e l h U B D K N:= G6_forecast F R P e l h hG K N hK hx hN hz Hq
    (Q2 F R J P Z M H ν Ht Zp) (fun _=> Q2 F R J P Z M H ν Ht Zp) (fun _=> Q2 F R J P Z M H ν Ht Zp)
variable {U B:ℝ} (hU:0<U)
include ν hU in
theorem G9 (hB:0<B)(hd:AppointedH140Through h e)(he:AppointedH140Through h l) : RoundPoint F P t A hd he U B p K N:= by
    apply upheave F P R Z M ν H hK hx hN hz t Ht.running (Zp.connects ..) (YPose F J P Z M H Ht Zp) (YPose F J P Z M H Ht Zp)
       (YPose F J P Z M H Ht Zp) hU hB p (G1 F J P Z M H ν Ht Zp hU hB) (G1 F J P Z M H ν Ht Zp hU hB) _ _
        (corridor F J P Z M H t Ht.running (Zp.accrue h) (Ht.positions _ _ _ hU hB hK hx hN hz p)) hd he (fun _=> Zp.connects ..) (fun _=> Zp.connects ..)
    all_goals
       intro K N hK hx hN hz; obtain ⟨D,_,F'⟩:=booth F R J P Z M H ν Ht Zp Hq hK hx hN hz (h:=(_)) (e:=Ceiling _ _) (l:=Ceiling _ _); exact ⟨D,F' U B⟩
end Batch
end YM.Integration.GradedFar
