import YM.GradedFar.Coin
import YM.GradedFar.Increment
/-!
# Raw W basis accounting and its adjustment

Actual orientation of the expansion. Use substitution in arguments independently, and finite generating
match on each order needed. Caps already fixed at h. Preparing in particular for G9 inputs using
W vs H before calendar costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
namespace Playbill
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open Fork (Sold Safe)
open Tickets
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Post" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "Before"=> Scale.Measure.start (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
local notation "PΣ" => Scale.Measure.adjust (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n m h:ℕ}
local notation "V"=> Sec G h
variable {X I:Type*}{φ:Filter X}{B W:X→I→ℝ}{K:X→I→Prop}
   {t:X→ℝ}(he:Coins φ K B t)
include H in
lemma raw : Before h= Facets.actMark (mirror (PΣ h)) (Post h):= by
 have hB:= ((H.details.toServed.toPosted.toQuoted.toContract.joint 0 h).2.2).scale
 rw [Scale.Measure.outlook,Facets.acts,hB.turn',Facets.acts_h]

def attends (u:V)(a: Toon G h) : PowerSeries ℂ := PowerSeries.mk (fun i=> coord a (coeff i (PΣ h) u))

theorem arrange {A B:Arenas G}{W:Guard G h}(hv:A h=Facets.actMark W (B h))(v:ListInput G n h)(x:Points n)(k:ℕ):
    coeff k (sent A h x v) = ∑ i∈Normalize.tally k n, coeff (i none) (sent B h x (pulseU i W v)):= by
 by_cases hx: x∈conf n
 · simp_rw [cashed _ _ hx,hv]; exact seen ..
 simp_rw [sent,coeff_mk,declared,dif_neg hx]; simp
include H he in
lemma start_price (f:X→I→Points n)(H':∀ u:ListInput G n h,Prospects φ K B (fun i j=> sent Post h (f i j) u)) (u:ListInput G n h) :
    Prospects φ K B (fun i j=> sent Before h (f i j) u):= by
 intro k; simp_rw [arrange (A:=Before) (B:=Post) (raw Z M H)]; exact Fork.Sold.sum he.spaces (fun _ _=> H' _ _)
lemma as_is {A:Arenas G} (u:ListInput G n h)(x: Points n): sent A h x u=
    ∑ i:Picks G (Ceiling n h), PowerSeries.C (multipliers u i)*sent A h x (basisWord i):=by
 apply PowerSeries.ext; intro j; simp_rw [map_sum,coeff_C_mul,sent,coeff_mk]; exact basis_sum (declared A h x j) u
lemma crop_as_is {A:Arenas G}(u:ListInput G n h)(x:Points n)(p:ℕ)(t:ℝ) : appointedH140Crop p t (sent A h x u)=
    ∑ i:Picks G (Ceiling n h), multipliers u i*appointedH140Crop p t (sent A h x (basisWord i)):=by
 conv_lhs=>rw [as_is,map_sum];
 refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [crop_eq,coeff_C_mul,Finset.mul_sum]; exact Finset.sum_congr rfl fun j _=> by ring
lemma adjust_compare (x:Points n)(v:ListInput G n h): sent Post h x v=
    ∑ i:Picks G (Ceiling n h), (∏ j, attends Z (v j) (i j))*sent Before h x (basisWord i):=by
 apply PowerSeries.ext; intro k; rw [arrange (A:=Post) (B:=Before) (W:=PΣ h) rfl,map_sum]
 simp_rw [Constants.admits,attends,coeff_mk]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; simp_rw [sent,coeff_mk]
 exact basis_sum (declared Before h x (j none)) (pulseU j (PΣ h) v)

-- continuous cost on compact trajectory in conf of Before kernels follows Post by exact inverse. Source later.
include H
lemma pre_continuous (k:ℕ)(v:ListInput G n h) : ContinuousOn (fun x=> coeff k (sent Before h x v)) (conf n):=by
 simp_rw [arrange (A:=Before) (B:=Post) (raw Z M H),sent,coeff_mk]; exact continuousOn_finsetSum _ fun i _=> kernel_continuous Z M H _ _
end Playbill
end YM.Integration.GradedFar.Tariff
