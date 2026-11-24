import YangMills.WilsonProof.NativeSupport.Commissioned140.AppointedOrdinaryScope.Measured
import YM.GradedFar.Snow
import YM.GradedFar.Weekday
import YM.GradedFar.Pan
import YM.Integration.WilsonPositionPrescribedFrame
import YM.Integration.WilsonPositionHomogeneousComparison
import YM.SignedWilsonExpansion.Kane.Finale
/-!
# Additional stronger clock entry point and continuation for the given Match and Run

Primary results also in `Measured` (`second` & `second_of_poseFit`).
Here derive (F.3) measured & field budget **from** previous (C5) compact PoseFit hypotheses,
`Stamps` & `Session`. Need same clock (including t′ℓ~g) for those Store & Rose compact tests, and *no*
G1, G6, G9 from buyer for second. Then compile strong continuation next requiring more votes
of PoseFit and earlier Leading & Reader inputs. See README on the distinctions.

Note namespace `Trace.Pilot.Coupling` is the previous kinetic hypothesis in supplied project. We
prove it on the exact t without assuming the loop claim or a positive tricubic estimate directly at t,
using the F.3 calibration method of proof (earlier hypothesis at W in its own gauge, t′~g etc).
Doesn't construct election data and Pose bills. Also see pins/build compatibility noted in README.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
open Function Filter Set PowerSeries
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score Enh FVA2.GradedFar
open scoped Topology BigOperators Classical
open Batch Tariff.Ballot
variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G)
    {hG:G.Simple} (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)) )
    {σ : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match Z hG M σ true)
local notation "A" => Scale.Measure.outlook Z.scheme Z.criterion
local notation "g" => strength G
local notation "t" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "W" => WilsonPositionPrescribedFrame.positioned F J Z.store
local notation "Jw" => WilsonPositionHomogeneousFrame.homogeneous F J Z
-- supply C5 diagnostics. with finite Fray costs on that vote; no comparison estimates from Main.Match on the physical values.
-- not using shadow W definitions to state costs.
lemma tested_receipt (r:ℝ) : WilsonPositionThermometerReading.tested F W Z.criterion r = (Rose.test Z.criterion).applyTo (readingLog F W r) := rfl -- parentheses may semireducible
variable (lead:Leading F J)
include lead
lemma at_store (h:ℕ): FitsSat F W Z h:=by
 filter_upwards [_root_.YM.Integration.WilsonPositionPrescribedFrame.original F J Z.store lead h, (show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin)] with r hr hh
 exact ⟨WilsonPositionPrescribedScreen.hierarchy F W h r, hr, fun n s v=> (WilsonPositionPrescribedScreen.actual F W h n s v hh).symm⟩
include H
-- avoid Unicode macros in variable command
variable (D:Fray ((WilsonPrescription.store Z).measure 6))
   {U:ℝ→Normalize.Change G 6}{τ:ℝ→ℝ}{q p:ℕ}
   (H₁: Stamps F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z p q 6 D U τ)
   (H₂: Session F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z (Rose.test Z.criterion) p q 6 τ U)
include H₁ H₂
lemma supplied_measure (hp:1≤p) : Coupling G t:= by
 obtain ⟨C,hc,H'⟩:= tested_continuum F W M H τ D U (at_store F J Z lead 6) H₁ H₂ hp
 simp_rw [← tested_receipt F J Z] at H'; let k:= p-1; apply poseFit_coupling hG F J Z τ k H₁.posted (C:=C)
 exact H'.mono (fun r hr=>by simpa only [Complex.ofReal_mul,show k+2=p+1 from (by unfold k; omega)] using hr)
-- user facing theorem. even relative to earlier C5 only. reading T -> ∞ unrestricted
local notation "Z*"=> GroupS.gaugeN Z.scheme Z.criterion M
theorem second_vote (hp:1≤p)(ν:ℝ) (hd : AppointedH140Through l d) (he : AppointedH140Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S' : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S') (hy : S' ⊆ Outside m)
    (j : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ᶠ r in trail, ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ K, ∀ y ∈ S',
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
      ∀ (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G e), Box u L → Box v L →
        ‖appointedH140Crop j (t r) (fullSeries A (Z* ν) (-Real.log T) hd he x y u v) -
            croppedResponse A (Z* ν) (-Real.log T) hh he y v j (t r) (croppedVector A h j u x (t r))‖ ≤
          C * ((T^(h+1))⁻¹ + (g r)^(j+1)) * (1+Real.log T)^k :=
 second F J Z M H ν (supplied_measure F J Z M H lead D H₁ H₂ hp) hd he hh K S' hK hx hS hy j L hL

omit H₁ H₂ H lead
open Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Week Tariff.Billboard
open Maxwell.Free WilsonPositionPrescribedScreen
local notation "R*"=> WilsonPositionHomogeneousFrame.turn F J Z
lemma pose_assign {r:ℝ}(ha:Bijective (stand (R* h r)))(v:Sec G h): assign Jw r h v= assign W r h (stand (R* h r) v):= by
 let L:= fields R.family.labels h; change W r h (WilsonPositionHomogeneousFrame.change F J Z h r (L.symm v)) = W r h (L.symm _)
 rw [WilsonPositionHomogeneousFrame.change,dif_pos ha]; congr 1
 simp only [L,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,LinearEquiv.ofBijective_apply]
include lead
lemma connected : Connected F W:= Included_chain F W fun d=> include_j F W (Nat.le_succ _) (_root_.YM.Integration.WilsonPositionPrescribedFrame.adjacent F J Z.store lead d)
lemma stored_axes (d:ℕ): ∀ᶠ r in trail, Axil F W r d:= by
 filter_upwards [(WilsonPositionPrescribedScreen.original F J lead Z.store d).2,axile F J lead d] with r hr he
 apply axial_preserved F J W r he (WilsonPositionPrescribedScreen.correction F J Z.store d r); intro v; let L:= fields R.family.labels d; change J r d (WilsonPositionPrescribedFrame.change F J Z.store d r (L.symm v))=J r d (L.symm _)
 rw [WilsonPositionPrescribedFrame.leg F J Z.store hr.2.1]
variable (ht:Coupling G (WilsonPositionHomogeneousFrame.reading F J Z))
include H ht
theorem earning : Prepared F W Jw Z t:= by
 let h:= Coupling.conforms hG ht; let P : WilsonPositionHomogeneousCoefficients.Warrant Z:= WilsonPositionHomogeneousCoefficients.purchased Z H
 have he (d:ℕ):∀ᶠ r in trail,∀ v:Sec G d, assign Jw r d v= assign W r d (stand (R* d r) v):= (h.eventually (WilsonPositionHomogeneousNear.invertible Z d)).mono fun r hr v=> pose_assign F J Z hr v
 refine ⟨fun d=>?_,fun d=> ((stored_axes F J Z lead d).and (he d)).mono (fun r hr=> axial_preserved F W Jw r hr.1 _ hr.2),fun h d p=> Included_turn F W Jw p (connected F J Z lead _ _ p) (R*) (fun r=>WilsonPositionHomogeneousNear.includes Z P p (t r)) he⟩
 refine accrual W Jw Z P (R* d) (he d) (fun q=>?_)
 obtain ⟨c,hc,H⟩:= WilsonPositionHomogeneousNear.expansion Z d q; let u:= tendsto_nhdsWithin_iff.mpr (show Tendsto t trail (𝓝 0) ∧ ∀ᶠ r:ℝ in trail, t r∈ Ioi 0 from ⟨h,ht.positive⟩)
 exact ⟨c,hc, ((u.eventually H).and ht.positive).mono fun r hr=>by rw [abs_of_pos hr.2]; exact hr.1⟩
lemma assemble (hc:∀ h:ℕ,0<h→ JointTicket F W Z h) (he:∀ (n h:ℕ), 0<n→0<h→fixedPose F W Z t h n)
    (hz:∀ {n m:ℕ},∀ (K:Set (Points n))(N:Set (Points m)){U B:ℝ}, IsCompact K→ K ⊆ conf n→ IsCompact N→ N ⊆ Outside m→ 0 < U→ 0<B→ 0<n+m→∀ (p h:ℕ),0<h→GridPose F W Z t K N h U B p): Pose F W Z t:=
 census F W Z M H ht ((stored_axes F J Z lead 0).mono fun r h=> h.unit) hc he hz
end YM.Integration.GradedFar
