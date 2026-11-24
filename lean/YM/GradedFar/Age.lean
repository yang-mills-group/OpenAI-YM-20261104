import YM.GradedFar.Compass
import YM.GradedFar.Gloss
import YM.Integration.WilsonPositionThermometerGradedSource
import YM.GradedFar.Azure
import YM.GradedFar.Acre
import YM.GradedFar.Occasion
import YM.GradedFar.Garden
import YM.GradedFar.Tint
import YM.GradedFar.OrbitInk
import YM.GradedFar.Corner
import YM.GradedFar.Dawn
import YM.GradedFar.Separated
/-!
# Universal consequences on the actual Frame, after `second_vote`

Convenience: the Budget assertions cited in README and the simple version of using the C5 inputs on the
whole required physical data. No need to first build such a bundle to use `second_vote` (the asked-for
lemma with its previous hypotheses).

`J` is the physical frame on the initial election (sec Bel as in supplied Frame setup), then `positioned`
W. All corollaries here use the same positions and Reading as in `Prior`, never install a posterior
or read out a phase-dependent clock. Real physics budgets required at this setup are explicitly
hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace M2Continuation
open Function Filter Set PowerSeries MeasureTheory Metric
open Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume
open Climb Trace.Pilot PhysMS OPE OPE.Orbits
open XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open MS MS.Native MS.Land MS.Fleet
open Dframe O O.Score O.Enh FVA2.GradedFar
open scoped Topology BigOperators Classical
variable {G : Gauge} {C: Family G} {n m h l p:ℕ} {d:Fin n→ℕ} {e:Fin m→ℕ}
variable {R: PhysicalNext.Repeat.Legato.Run G} {f:Extraction.Order} {S:Table R.family.book}
    (U:Final R.family f S) (J:ℝ→PhysMS.tower S) (lead:Leading U J) (N:WilsonPrescription G)
    (Q : Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
local notation "t"=> WilsonPositionHomogeneousFrame.reading U J N
local notation "W"=> WilsonPositionPrescribedFrame.positioned U J N.store
local notation "Φ"=> WilsonPositionHomogeneousFrame.homogeneous U J N
local notation "V"=> Scale.Measure.outlook N.scheme N.criterion
local notation "g"=> strength G
include lead
-- Verify that WPTR W, spelled with all-six in #print of the actual prescription, really keeps
-- the specified grades and masks on every actual W request.
section
open Maxwell.Free WilsonPositionThermometerGradedSource
lemma thermostat_masks : ∀ᶠ r in trail, ∀ (x:Points 3), x∈conf 3→∀ s:Rose.Badge,
    WilsonPositionThermometerReading.sample U W r x s = PhysMS.measured U none (W r) (d:=fun i=> (grade i).val) (source R.family s) r x:=by
 have h := connected U J N lead
 filter_upwards [eventually_all.mpr (fun i:Fin 3=> h 6 ((grade i).val) (Nat.le_of_lt_succ (grade i).isLt)),
    (show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin)] with r hr hp x hx s
 let d:Fin 3→ℕ:= fun i=>(grade i).val; have he(i:Fin 3):d i≤6:=Nat.le_of_lt_succ (grade i).isLt
 let f(i:Fin 3): RG17.Free R.family (d i) := source R.family s i
 let H₀(i):=(W r (d i)) (f i); let v:= fun i=> fields R.family.labels (d i) (f i)
 have hx'(i:Fin 3): assign W r (d i) (v i)=H₀ i:=by unfold v H₀ assign; rw [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
 have hi (i:Fin 3): W r 6 (WilsonPositionThermometerReading.leg R.family s i)= U.sector.derivatives.rise (he i) (H₀ i):=by
    obtain hf:= (hr i (v i)); calc
      _ = assign W r 6 (fields R.family.labels 6 ((Maxwell.Free.scheme R.family.labels).rise (he i) (f i))) := by
        rw [assign, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]; exact congrArg (W r 6) (WilsonPositionThermometerGradedSource.promoted R.family s i).symm
      _ = _ := by rw [Tariff.Billboard.eng_rise]; change assign W r 6 (up (he i) (v i))=_; rw [hf, hx' i]
 change S.classMoment S _ (r•x) (fun i=> W r 6 (WilsonPositionThermometerReading.leg R.family s i)) = _
 simp_rw [hi]; exact AllOrder.Leading.moment_inclusion U.room.kernel.laws.toSymmetric U.phase.transport.injection he (Work.A05.smul_conf hp hx) H₀
end
open Batch Auth Tariff Tariff.Playbill Tariff.Ballot Tariff.Crosser Tariff.Sunshine Neighbor
omit lead
/-- Predecessor inputs at time of second inequality suffice there. Before using (`M2Continuation`) also deliver
from PoseFit its compact and joint and grid estimates as indicated. Exact same Reading/Frame; no θ-supplier change.
Pose takes the clock hypothesis (`Coupling`), which use `supplied_measure`, or `poseFit_coupling`, as proved.
See `Batch.Pose`, and `GradedFar.assemble` (Compass) deriving zero cases. -/
abbrev Prior (U:Final R.family f S) (J:ℝ→ PhysMS.tower S) (N:WilsonPrescription G) := Pose U (WilsonPositionPrescribedFrame.positioned U J N.store) N (WilsonPositionHomogeneousFrame.reading U J N)
variable {lead}
variable {hG:G.Simple} (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ:MS.Land.Prescription (Press.portDeck G)}
    (matched:Main.Match N hG M σ true)(ν:ℝ) (hp:Prior U J N) (HL:LogTrace U Q.port)
-- explicitly lead
variable (lead)
include lead matched hp
lemma matched_expenses : Batch.Prepared U W Φ N t:= GradedFar.earning U J N M matched lead hp.running
lemma area_prices (h:ℕ) : (∀ I:Set ℝ, IsCompact I → ∀ m:ℕ, 1 ≤ m → Lounge.StampScale Φ N M ν h m t I) ∧
    ∀ (A B:ℝ), 0 < A→ 0<B → G1Wide Φ N M ν h t A B:= by
 let f:= matched_expenses U J lead N M matched hp; refine ⟨fun _ hI p hx=> Lounge.stampScale Φ N M ν h p matched ?_ ?_ ?_ hp.running hx hI,fun _ _ ha hb=>Batch.G1 U W Φ N M matched ν hp f ha hb ⟩
 exacts [(coupons U W Φ N M matched ν hp f (Nat.le_refl 1)).1,(coupons U W Φ N M matched ν hp f hx).1,(coupons U W Φ N M matched ν hp f hx (h:=h)).2]
include ν in
lemma coat (h:ℕ): Fork.Coat U Q Φ h:= Batch.Q2 U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp)
include HL
variable {K:Set (Points n)}{E:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hE:IsCompact E)(hy:E⊆ Outside m)
include hK hx hE hy
-- user consumes these on h=..., common precision l, k etc
include ν in
theorem G6_true : ∃ D:ℝ,0≤ D ∧ ∀ A B, G6 U Q Φ d e h A B D K E:=
    booth U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp) HL hK hx hE hy
variable {A B a:ℝ}(ha:0<a)(hA:0<A)(hB:0<B)
include ν hA hB in
theorem G9_true (hd:AppointedH140Through l d)(he:AppointedH140Through l e): RoundPoint U Φ t V hd he A B p K E ∧
    ∀ h p q L (u:Fin (n+m)→ℕ)(he: AppointedH140Through h u), RoundFull U Φ N t A B K E L p q he := by
 obtain f:= matched_expenses U J lead N M matched hp; exact ⟨ Batch.G9 U Q W Φ N M matched ν hp f HL hK hx hE hy hA hB hd he, fun h p q L u he=> Batch.roundFull U Q W Φ N M matched ν hp f HL hA hB hK hx hE hy he L p q⟩
local notation "Y"=> GroupS.gaugeN N.scheme N.criterion M ν
include hA hB in
-- explicit first comparison
lemma m2first (p:ℕ)(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l) : ∃ c:ℝ,0≤c ∧ ∃ k:ℕ,∃ T₀≥ (2:ℝ), ∀ᶠ r in trail,
    ∀ T:ℝ,T₀≤T→ T≤ A*g r^(-B) →∀ x∈K,∀ y∈E, ∀ o:E4,∀ (v:Viewers U)(u:AppointedH140Inputs G d)(w:AppointedH140Inputs G e), Box u 1→ Box w 1→
    ‖atLength U Φ v o r T x y u w-appointedH140Crop p (t r) (fullSeries V Y (-Real.log T) hd he x y u w)‖ +
      rowPrice (atCenter U Φ h v o r T y w - croppedResponse V Y (-Real.log T) hh he y w p (t r)) ≤ c*T^(FVA2.GradedFar.power e)*g r^(p+1)*(1+Real.log T)^k:=
    first_price U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp) HL hd he hh hK hx hE hy hA p hB
variable {η:ℝ} (hη:η<1)
include hA ha hη
theorem stage_m3 (k:ℕ)(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l): ∀ᶠ B:ℝ in atTop, ∀ᶠ p in atTop,
    BeforeInverse U Φ Q N M ν t hd he hh K E a A η B k p:=
    Batch.M3 U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp) HL hd he hh hK hx hE hy hA ha hη k
-- Supplementary cutoff price on genuine *cutoff renderer* m_N (not T_o, or approximation thereof). Auth for constant-reference version. See notes on order of U's hypotheses.
-- This is not a premise of the continuum comparisons. Use actual #period-fullUV estimates only here.
theorem also_cut (hQ:FullVolume.FixedBounds R.family)(hS:PositionsUV R.family Extraction.Sequence.full)
    (H':R.family.Makes)(δ:ℝ)(hd':0<δ)(k:ℕ)(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l): ∀ᶠ B in atTop,∀ᶠ p in atTop, ∀ᶠ q in atTop,Auth.Before_cut U Q Φ N M ν hd he hh t K E a A η B k p q δ:= cutoff_M3 U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp) HL hA hK hx hE hy hQ (Auth.journals hS) H' hd he hh ha hη δ hd'.le k
omit hE hy hA ha hη
-- shapes compact costs, relative continuation to assembly H on its growing/receding part. Ordinary Kernel for physical reader uses (separate) pricess G6 & G7.
theorem continuum_rows (hd:AppointedH140Through l d)(p:ℕ):
    (∃ D:ℝ,0≤ D ∧ ∀ᶠ r in trail,∀ v:Viewers U,∀ o x,∀ h:x∈ K,∀ u, Box u 1→
        ‖TrueCompact U Φ v r o x u-appointedH140Crop p (t r) (msCompact N M ν hd ⟨x,hx h⟩ u)‖ ≤ D*(t r)^(p+1)) ∧
    ∀ L:TraceOrder n, ∃ D:ℝ,0≤ D ∧ ∀ᶠ r in trail,∀ v:Viewers U,∀ o x, x∈K→ ∀ u:AppointedH140Inputs G d, Box u 1 →
        ‖δ L (fun x=> TrueCompact U Φ v r o x u) x- δ L (fun x=> appointedH140Crop p (t r) (msRow N M ν hd u x)) x‖ ≤ D*(t r)^(p+1):=
    ⟨ Batch.comparisonG U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp) HL hd hK hx p,
      fun L=> day U W Φ Q N M matched ν hp (matched_expenses U J lead N M matched hp) HL hd hK hx L p⟩
theorem ordinary_ope (hd:AppointedH140Through l d)(hh:h≤l)(p:ℕ):
    (∃ D:ℝ,0≤ D ∧ ∀ᶠ r in trail,∀ o x,x∈K → ∀ u:AppointedH140Inputs G d, Box u 1 → width (packet U Φ Q h o r x u - msVector N M ν u x p h (t r)) ≤ D*(t r)^(p+1)) ∧
    ∀ (L:TraceOrder n)(a:Toon G h),∃ D:ℝ,0≤D ∧ ∀ᶠ r in trail,∀ o x,x∈K → ∀ u:AppointedH140Inputs G d,Box u 1 →
        ‖δ L (fun x=> coord a (packet U Φ Q h o r x u)) x- δ L (fun x=> coord a (msVector N M ν u x p h (t r))) x‖ ≤ D*(t r)^(p+1) :=
    ⟨ Batch.comparisonOPE U Q W Φ N M matched ν hp (matched_expenses U J lead N M matched hp) HL hd hh hK hx p,
      fun L a=> Batch.derivativesOPE_coord U W Φ Q N M matched ν hp (matched_expenses U J lead N M matched hp) HL a hd hK hx L p⟩
end M2Continuation
end YM.Integration.GradedFar
