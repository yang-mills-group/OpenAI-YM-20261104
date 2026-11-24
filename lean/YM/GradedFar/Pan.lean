import YM.GradedFar.Batch
/-!
# Consequences at M.3 precision table from the Pose and preparation

M.2 first and its costs, before elaborating the reader inverse. Public representations
`BeforeInverse` & actual (non-grid) comparison to `MS_Data` supplied by original `Main.Match`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
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
    {t:ℝ→ℝ}
local notation "g∴"=> strength G
local notation "A" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "W" => GroupS.gaugeN (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z) M ν
variable (Ht: Pose F J Z t) (Zp: Prepared F J P Z t) (Hq:LogTrace F R.port)
variable {n m d h:ℕ} {e:Fin n→ℕ}{l:Fin m→ℕ} (he:AppointedH140Through d e)(hl:AppointedH140Through d l)(hh:h≤d)
variable {K:Set (Points n)}{N:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N⊆Outside m)
variable {U B:ℝ}(hU:0<U)
-- center singleton (any positions of the proper-subarray stock)
lemma little : {(0:Points 1)} ⊆ conf 1 := fun _ _ _ _ _=>Subsingleton.elim ..
lemma none_out : {(0:Points 0)} ⊆ Outside 0 := singleton_subset_iff.mpr nofar_ok

include H Hq Ht Zp he hK hx hU
include hl hh hN hz in
theorem first_price (p:ℕ)(hB:0<B):
    ∃ C:ℝ,0≤C ∧ ∃ k:ℕ,∃ T₀:ℝ,2≤ T₀ ∧ ∀ᶠ r in trail,
    ∀ T:ℝ,T₀≤T→ T≤ U*(g∴ r)^(-B) → ∀ x∈K,∀ y∈N,∀ o:E4,∀ (v:Viewers F)(u:AppointedH140Inputs G e)(w:AppointedH140Inputs G l), Box u 1 → Box w 1 →
    ‖atLength F P v o r T x y u w-appointedH140Crop p (t r) (fullSeries A W (-Real.log T) he hl x y u w)‖+
        rowPrice (atCenter F P h v o r T y w-croppedResponse A W (-Real.log T) hh hl y w p (t r)) ≤
            C*T^(FVA2.GradedFar.power l)*(g∴ r)^(p+1)*(1+Real.log T)^k :=
    first F P Z M H ν Ht.running hK hx hN hz p he hl hh (fun _=> (G1 F J P Z M H ν Ht Zp hU hB).forecast)
      (G9 F R J P Z M H ν Ht Zp Hq hK hx hN hz hU hB he hl)
      (G9 F R J P Z M H ν Ht Zp Hq isCompact_singleton little hN hz hU hB _ hl)
include hN hz hl hh in
theorem M3 {η a:ℝ}(ha:0<a)(hη:η<1)(q:ℕ):∀ᶠ B in atTop,∀ᶠ p in atTop,
    BeforeInverse F P R Z M ν t he hl hh K N a U η B q p := before_of_prices F R P Z M H ν Ht.running he hl hh hK hx hN hz Hq
      (Q2 F R J P Z M H ν Ht Zp) (fun _=>Q2 F R J P Z M H ν Ht Zp) (fun _=> Q2 F R J P Z M H ν Ht Zp) ha hU hη
      (fun _ hB _=> (G1 F J P Z M H ν Ht Zp hU hB).forecast)
      (fun _ hB _=> G9 F R J P Z M H ν Ht Zp Hq hK hx hN hz hU hB ..)
      (fun _ hB _=> G9 F R J P Z M H ν Ht Zp Hq isCompact_singleton little hN hz hU hB ..) q
-- downstream ANY aperture U >0, instantiate say U=1 avoiding extra hypothesis.
omit hU
include hh in
theorem comparisonOPE (p:ℕ): ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀ o x,x∈ K → ∀ u:AppointedH140Inputs G e,Box u 1→
    width (packet F P R h o r x u - msVector Z M ν u x p h (t r)) ≤ C*(t r)^(p+1) :=
    ms_ope Z M H ν F R P Ht.running (Λ:=1) zero_lt_one hK hx he hh Hq (Q2 F R J P Z M H ν Ht Zp) (fun _=>Q2 F R J P Z M H ν Ht Zp)
        (fun _ hB=> (G1 F J P Z M H ν Ht Zp zero_lt_one hB).forecast)
        (fun _ hB=> G9 F R J P Z M H ν Ht Zp Hq isCompact_singleton (singleton_subset_iff.mpr ok_wall) isCompact_singleton none_out zero_lt_one hB ..)
        (fun _ hB _=> G9 F R J P Z M H ν Ht Zp Hq hK hx isCompact_singleton (singleton_subset_iff.mpr ok_wall) zero_lt_one hB ..)
        (fun _ hB _=> G9 F R J P Z M H ν Ht Zp Hq isCompact_singleton little isCompact_singleton (singleton_subset_iff.mpr ok_wall) zero_lt_one hB ..) p

theorem comparisonG (p:ℕ): ∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀ v:Viewers F,∀ o x,∀ h: x∈ K,∀ u, Box u 1→
    ‖TrueCompact F P v r o x u - appointedH140Crop p (t r) (msCompact Z M ν he ⟨x,hx h⟩ u)‖ ≤ C*(t r)^(p+1):=
    ms_at_compact Z M H ν F P Ht.running (Λ:=1) zero_lt_one hx he p (B:=1) zero_lt_one (G9 F R J P Z M H ν Ht Zp Hq hK hx isCompact_singleton none_out
        zero_lt_one zero_lt_one ..)
end YM.Integration.GradedFar.Batch
