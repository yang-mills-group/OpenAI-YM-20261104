import YM.GradedFar.Batch
import YM.GradedFar.Sunlight
/-!
# Use at exact positions in RoundMeter.(i) after removing its grid hypotheses

The point purchase in Epoch and this extra ticket require all derivative-program
continuation through corresponding caps. No estimating-regulator assertion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Tariff.Tickets
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m Ux Ym p h l :ℕ}
local notation "g∴"=> strength G
local notation "X" => Scale.Measure.outlook Z.scheme Z.criterion
include H Ht hF
lemma smooth_post (v:ListInput G n h) (i:ℕ) : ContDiffOn ℝ ∞ (fun x=> coeff i (sent X h x v)) (conf n):= by
 choose A ha using fun i=>futureWins F P Z M H Ht.running (hF.connects (i+1) i _) (YPose F J P Z M H Ht hF); exact
    Air F P Z M H Ht.running (fun h=>hF.connects ..) (fun _=>YPose F J P Z M H Ht hF) A ha v i
variable {U B:ℝ}(hU:0<U)(hB:0<B){K:Set (Points n)}{N:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
local notation "P∥" => moving G U B
open Fork (Sold Safe)
variable {I:Type*} {W:Calendar→I→Prop} {z: Calendar→I→Points (n+m)}(he:∀ p i, W p i → Fits K N p.2 (z p i))
include Hq hU hB hK hx hN hz he
local notation "B*" => WithTax p (moving G U B) W (fun i _=> Δlog i) (t ∘ Prod.fst)
include ν in
private lemma first_jet (v:ListInput G (n+m) h)(u:Calendar→I→ Viewers F): B* (fun i j=> frank F P (u i j) h i.1 (z i j) v)
    (fun i j => sent X h (z i j) v):= by
 refine ⟨fun i=> Road.formal_bill Z M H hK hx hN hz he i v,?_⟩; have H₁(h:ℕ): HorizonPaid F P R n m h U B:= by
    intro K N hK hx hN hz; obtain ⟨D,_,H⟩:= booth F R J P Z M H ν Ht hF Hq hK hx hN hz (h:=h) (e:=Ceiling n h) (l:=Ceiling m h); exact ⟨D,H U B⟩
 let X':= YPose F J P Z M H Ht hF (h:=h) (n:=n+m); obtain ⟨j,c,hc,H'⟩:= pays_form F P R Z M ν H hK hx hN hz t Ht.running (hF.connects ..) X' (YPose F J P Z M H Ht hF) (YPose F J P Z M H Ht hF)
    hU hB p (G1 F J P Z M H ν Ht hF hU hB) (G1 F J P Z M H ν Ht hF hU hB) (H₁ h) (H₁ (h+1))
    (corridor F J P Z M H t Ht.running (hF.accrue h) (Ht.positions h _ _ hU hB hK hx hN hz p)) he v u
 refine ⟨j,c*2^(p+1),by positivity,?_⟩; filter_upwards [H',closer rising Ht.running (p+1) (hG:=hG),moneySafe] with p' hp hv ht i hi
 exact (hp i hi).trans ((mul_le_mul_of_nonneg_left hv (mul_nonneg hc (pow_nonneg (zero_le_one.trans ht) _))).trans_eq (by ring))
-- all assigned ratios & programs. Uses (co-committed) Pose etc. Actual derivative of THAT viewer moment.
include ν in
lemma price_jet (L:TraceOrder (n+m))(v:ListInput G (n+m) h)(u:Calendar→I→Viewers F): B* (fun i j=> δ L (fun x=>frank F P (u i j) h i.1 x v) (z i j))
    (fun i j=> jetCost L X h v (z i j)):=by
 choose A ha using fun i=>futureWins F P Z M H Ht.running (hF.connects (i+1) i _) (YPose F J P Z M H Ht hF)
 let H0 : Coins P∥ W (fun i _=> Δlog i) (t ∘ Prod.fst):= ⟨Road.safety, (Coupling.conforms hG Ht.running).comp rising⟩
 induction L generalizing h with
 | nil=>
    simp_rw [δ,jetCost_zero]; exact first_jet F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz he v u
 | cons i L ih=>
    let w:= v i.1; let α:= A h i.2 w; let c(x:ℝ)(j:Toon G (h+1)):= coord j (push F P h i.2 x w); let Y(j:Toon G (h+1)):= update (climbing v) i.1 (theory j)
    have hc(j): B* (fun i (l:I)=> c i.1 j) (fun _ _=> α j) := by
       have he:= ha h i.2 w j; refine ⟨fun k=> Fork.Sold.closed _,?_⟩; obtain ⟨c,hc,hc'⟩:= (he.good p).cost; exact Fork.Sold.bounded hc ((poses hc').mono (fun i hi l _=> hi ()))
    refine (WithTax.sum H0 Finset.univ (fun i _=> (hc i).mul H0 (ih (Y i)))).tran ?_ ?_
    · filter_upwards [poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin), Road.funded_forms hK hx hN hz he,
        poses (show ∀ᶠ r in trail,Going F P h r from hF.connects ..)] with r hr hi hx j hj; exact (physical_cons F P (hi j hj) hr hx (u r j) L i v).symm
    exact (Road.funded_forms hK hx hN hz he).mono fun p hp x hx=> (jetCost_cons F P Z M H Ht.running (fun _=> hF.connects ..)
       (fun _=> YPose F J P Z M H Ht hF) A ha (hp x hx) L i v).symm
end YM.Integration.GradedFar.Batch
