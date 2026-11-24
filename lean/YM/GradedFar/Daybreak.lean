import YM.GradedFar.Shine
/-!
# Derivative correlation comparison in H-frame

Endpoint relative to elected data/costs, any arity incl. empty. Zero-extension of MS only subject to
calls at conf in results. Compare after transfer as in entire `Match.eqconv`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Tariff Tariff.Sunshine Tariff.Playbill Tariff.Crosser FVA2.GradedFar.Cart
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (J P: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)(ν:ℝ)
local notation "V"=> Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "g∴"=> strength G
variable {t:ℝ→ℝ} (Ht:Pose F J Z t)(Hp:Prepared F J P Z t)(HL:LogTrace F R.port)
variable {n m h d:ℕ}
local notation "X"=> Points n
variable {e:Fin n→ℕ}(he:AppointedH140Through h e)
private lemma fit_fin {K:Set X}(T:ℝ){x:X}(hx:x∈K): Fits K ({(0:Points 0)}) T x:=by
 refine ⟨x,hx,0,Set.mem_singleton _,?_⟩; ext1 i; rw [show i=Fin.castAdd 0 i from Fin.ext rfl, forest_left]; exact rfl

def msRow (u:AppointedH140Inputs G e)(x:X): PowerSeries ℂ:= if h:x∈conf n then msCompact Z M ν he ⟨x,h⟩ u else 0
include H
lemma exchanged (u:AppointedH140Inputs G e)(x:X): msRow Z M ν he u x= sent V h x (GradedFar.raised he u):= by
 unfold msRow; split_ifs with h; rw [bookCompact Z M H]; ext1 k; simp_rw [cashed _ _ h, FormalCompact, coeff_mk]
 ext1 k; simp_rw [sent, map_zero, coeff_mk,declared,dif_neg h]; rfl
variable {K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n) (L:TraceOrder n)
include Ht Hp HL hK hx
theorem day (p:ℕ): ∃ D:ℝ,0≤D ∧ ∀ᶠ r in trail,∀ V₁:Viewers F,∀ o x, x∈K → ∀ u:AppointedH140Inputs G e, Box u 1 →
    ‖δ L (fun x=> TrueCompact F P V₁ r o x u) x- δ L (fun x=>appointedH140Crop p (t r) (msRow Z M ν he u x)) x‖ ≤ D*(t r)^(p+1):= by
 obtain ⟨b,hb,i,T,hT,H'⟩:= roundFull F R J P Z M H ν Ht Hp HL zero_lt_one zero_lt_one hK hx isCompact_singleton (singleton_subset_iff.mpr nofar_ok) he L p 0 -- T=1^ design
 have hV:0≤1+Real.log T:=by linarith [Real.log_nonneg (show (1:ℝ)≤ T from one_le_two.trans hT)]
 refine ⟨b*(1+Real.log T)^i*2^(p+1),by positivity,?_⟩
 filter_upwards [H',remaining_budget (hG:=hG) Ht.running (p+1), (strength_falls hG).eventually (Budget.upwards (B:=1) zero_lt_one (a:=1) zero_lt_one T)] with r hr he' hS v o x hv u hU
 obtain hq:=(hr T le_rfl (hS _ le_rfl) x (fit_fin T hv) o v u hU).1
 simp_rw [exchanged Z M H]; rw [← jet_value F J P Z M H Ht Hp he L p u (hx hv)]; refine le_trans hq ((mul_le_mul_of_nonneg_left he' (by positivity : 0≤ b*(1+Real.log T)^i)).trans_eq (by simp only [mul_pow,mul_assoc]))
end YM.Integration.GradedFar.Batch
