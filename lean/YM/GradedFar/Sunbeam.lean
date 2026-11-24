import YM.GradedFar.RoadMap
/-!
# All profiles & field labels -> G9 derivative version

Costs actual fields at o with mixed caps (or lift programming to common h per
`squeezed` row) in same true normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Batch
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Tariff.Tickets
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m p q h:ℕ}
local notation "g∴"=> strength G
local notation "X"=> Scale.Measure.outlook Z.scheme Z.criterion
variable {d:Fin n→ℕ}(hd:AppointedH140Through h d)
-- promote for all hands on a common dimension around the Ball; no continuity assumption
lemma snapshots (L:TraceOrder n) (f: Points n→MultilinearMap ℂ (fun _:Fin n=>Sec G h) ℂ)
    (h:∀ v:ListInput G n h,ContDiffOn ℝ ∞ (fun x=> f x v) (conf n)) (u:AppointedH140Inputs G d){x:Points n}(hx:x∈conf n):
    δ L (fun x=> f x (GradedFar.raised hd u)) x= ∑ i:Picks G d, multipliers u i * δ L (fun x=> f x (GradedFar.raised hd (basisWord i))) x:= by
 let m i:= multipliers u i; have hp(x:Points n): f x (GradedFar.raised hd u)=∑ i:Picks G d, m i*f x (GradedFar.raised hd (basisWord i)):= basis_sum ((f x).compLinearMap (fun i=> up (hd i))) u
 calc _ = δ L (fun x=> ∑ i:Picks G d, m i*f x (GradedFar.raised hd (basisWord i))) x:= (δ_congr (conf_open _) (fun a _=> hp a) L hx)
      _ = _:= by rw [δ_sum (conf_open _) _ _ (fun i _=> contDiffOn_const.mul (h _)) L hx]; exact Finset.sum_congr rfl fun i _=> δ_const_mul (conf_open _) (h _) _ _ hx
include H Ht hF
lemma contributions (L:TraceOrder n)(u:AppointedH140Inputs G d){x:Points n}(hx:x∈conf n): jetCost L X h (GradedFar.raised hd u) x=
    ∑ i:Picks G d, PowerSeries.C (multipliers u i)*jetCost L X h (GradedFar.raised hd (basisWord i)) x:= by
 ext1 k; have Xc (u:ListInput G n h) := smooth_post F J P Z M H Ht hF u k; simp_rw [sent,coeff_mk] at Xc; simp_rw [jetCost,map_sum,coeff_C_mul,coeff_mk,sent,coeff_mk]
 exact snapshots hd L (fun x=> declared X h x k) Xc u hx
variable {U B:ℝ}(hU:0<U)(hB:0<B){K:Set (Points n)}{N:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
local notation "P∥" => moving G U B
variable {I:Type*} {W:Calendar→I→Prop} {z: Calendar→I→Points (n+m)}(he:∀ p i, W p i → Fits K N p.2 (z p i))
include Hq hU hB hK hx hN hz he ν
local notation "B*" => WithTax p (moving G U B) W (fun i _=> Δlog i) (t ∘ Prod.fst)
variable {a:Fin (n+m)→ℕ} (ha:AppointedH140Through h a)
lemma tribute (L:TraceOrder (n+m))(u:Calendar→I→AppointedH140Inputs G a)(hc:∀ x i, W x i → Box (u x i) 1)(V:Calendar→I→Viewers F)(o:Calendar→I→E4):
    B* (fun i j=> δ L (fun x=> TrueCompact F P (V i j) i.1 (o i j) x (u i j)) (z i j))
        (fun i j=> jetCost L X h (GradedFar.raised ha (u i j)) (z i j)):= by
 let H0:Coins P∥ W (fun i _=>Δlog i) (t ∘ Prod.fst):=⟨Road.safety,(Coupling.conforms hG Ht.running).comp rising⟩
 let m' (k:Picks G a)(x:Calendar)(i:I):= multipliers (u x i) k
 have hm (k:Picks G a):Sold P∥ W (fun i _=>Δlog i) (fun _ _=>1) (m' k):= Fork.Sold.bounded (c:=1) zero_le_one (Eventually.of_forall fun x i h=> by
    rw [mul_one]; exact (multipliers_le zero_le_one _ k (hc x i h)).trans_eq (one_pow _))
 have hb(k:Picks G a):B* (m' k) (fun i j=> PowerSeries.C (m' k i j)):= by
    refine ⟨fun i=>?_,?_⟩
    · simp_rw [coeff_C]; split_ifs; exacts [hm _,Fork.Sold.zero]
    simp_rw [constant_crop,sub_self]; exact Fork.Sold.zero
 refine (WithTax.sum H0 Finset.univ (fun i _=> (hb i).mul H0 (price_jet F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz he L (GradedFar.raised ha (basisWord i)) V))).tran ?_ ((Road.funded_forms hK hx hN hz he).mono fun p hp x h=> (contributions F J P Z M H Ht hF ha L (u p x) (hp x h)).symm)
 filter_upwards [poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin), Road.funded_forms hK hx hN hz he, poses (eventually_all.mpr (fun i=> hF.connects h (a i) (ha i)))]
    with p hp hk hb i hi; dsimp only [m']; refine Eq.trans (snapshots ha L _ (true_views F P (V p i) hp) (u p i) (hk i hi)).symm (δ_congr (conf_open _) (fun x hx=> ?_) L (hk i hi)); exact Eq.trans (frank_inclusion F P ha hp (V p i) hb (u p i) hx) (atTable_within F P (V p i) a (u p i) (o p i) hp hx)

-- rewrite across arbitrary compact partial sums, for use at continuum observable and analytic token. Extra j budgets.
omit hK hx hN hz he hU hB Hq ν in
lemma jet_value (L:TraceOrder n)(p:ℕ)(u:AppointedH140Inputs G d){x:Points n}(hx:x∈conf n)(s:ℝ): appointedH140Crop p s (jetCost L X h (GradedFar.raised hd u) x)=
    δ L (fun x=> appointedH140Crop p s (sent X h x (GradedFar.raised hd u))) x:= by
 let v:= GradedFar.raised hd u; let f (i:ℕ)(x:Points n):= coeff i (sent X h x v)
 simp_rw [crop_eq,jetCost,coeff_mk]; rw [δ_sum (conf_open _) _ (fun (i:ℕ) x=> (s:ℂ)^i*f i x) (fun i _=> contDiffOn_const.mul (smooth_post F J P Z M H Ht hF v i)) L hx]; exact Finset.sum_congr rfl fun i _=> (δ_const_mul (conf_open _) (smooth_post F J P Z M H Ht hF v i) _ L hx).symm
end YM.Integration.GradedFar.Batch
