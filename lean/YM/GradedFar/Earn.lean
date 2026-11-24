import YM.GradedFar.Decree
/-!
# G9 value across the purchased grid and ALL admitted points

Uniform label costs; exercise receipts exactly from the indicated predecessors. There's an optional
stronger continuum shape derivative version here (`Batch.roundFull`). Only on actual continuum values (G.9),
not estimates on the regulator implementation in RoundMeter(ii). Preserve all v,o.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff.Crosser
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor
open Fork (Sold Safe)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
variable {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
variable {n m h:ℕ} {U B:ℝ}
local notation "Pt" => Points (n+m)
local notation "P∥" => moving G U B
local notation "g∴" => strength G
local notation "X" => Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {K:Set (Points n)}{N:Set (Points m)}(hK:IsCompact K)(hx:K ⊆ conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
variable (t:ℝ→ℝ)(ht:Coupling G t)(hμ: Included F J h (h+1) (Nat.le_succ h))
    (hX:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (n+m) h)
    (hY:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t (n+m) (h+1))
    (hQ:ClassExpansion F J (Scale.Measure.outlook Z.scheme Z.criterion) t 2 (h+1))
variable (hU:0<U)(hB:0<B)(k:ℕ)
    (hV:G1Wide J Z M ν h t U B)(hv:G1Wide J Z M ν (h+1) t U B)(hw:HorizonPaid F J R n m h U B)
    (hw': HorizonPaid F J R n m (h+1) U B) (ha:GridPower F J K N t U B (Scale.Measure.outlook Z.scheme Z.criterion) h k)
-- order of X? GridPower requires X argument; fix.

include hU hB hK hx hN hz H ht hμ hX hY hQ hV hv hw hw' ha
lemma pays_form {I:Type*}{W:Calendar→I→Prop}{z:Calendar→I→Points (n+m)}(hf:∀ p i,W p i→ Access K N p (z p i))
    (u:ListInput G (n+m) h) (v:Calendar→I→Viewers F): Sold P∥ W (fun p _=>Δlog p) (fun p _=>g∴ p.1^(k+1))
      (fun p i=> frank F J (v p i) h p.1 (z p i) u-appointedH140Crop k (t p.1) (sent X h (z p i) u)):=by
 obtain ⟨j,b,hb,hFF⟩:= (Road.true_bill F J R Z M ν (hG:=hG) hK hx hN hz hf (t:=t) hV (hw K N hK hx hN hz) u v).2
 obtain ⟨α,hα⟩:= futureWins F J Z M H ht hμ hQ
 obtain ⟨l,d,hd,Hh⟩:= campus F J R Z M ν H hK hx hN hz ht hμ hα hX hY hU hB u k hv hw' ha
 refine ⟨l,b+d,add_nonneg hb hd,?_⟩; filter_upwards [hFF,Hh,flatCost (hG:=hG) hU hB (k+1) j, poses (strength_positive hG),moneySafe] with
    p hr hs hp hg hx i h₁
 have hh:b*(wallet G p)^j*(p.1*p.2) ≤ b*Δlog p^l*g∴ p.1^(k+1):= by
   rw [mul_assoc b]; exact (mul_le_mul_of_nonneg_left hp hb).trans (mul_le_mul_of_nonneg_right
     (le_mul_of_one_le_right hb (one_le_pow₀ hx)) (by positivity))
 apply le_trans (opt _ _ (frank F J none h p.1 (z p i) u)) -- Neighbor.opt
 exact (add_le_add ((hr i h₁).trans hh) (hs (z p i) (hf p i h₁))).trans_eq (by ring)

variable {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:AppointedH140Through h d)(he:AppointedH140Through h e)
    (H₁:∀ i, Included F J (d i) h (hd i))(H₂:∀ i, Included F J (e i) h (he i))
include H₁ H₂
set_option maxHeartbeats 600000 in
theorem upheave : RoundPoint F J t X hd he U B k K N:= by
 let o(p:Calendar):= g∴ p.1^(k+1)
 let Ω:= Viewers F × ↥K × ↥N × E4 × {u:AppointedH140Inputs G d//Box u 1} × {v:AppointedH140Inputs G e//Box v 1}
 let x(i:Ω):Points n:=i.2.1.val; let y(i:Ω): Points m:= i.2.2.1.val; let χ(i:Ω): E4:=i.2.2.2.1
 let z(p:Calendar)(i:Ω):=forest (x i) (p.2 • y i)
 let V(p:Calendar)(i:Ω): Viewers F:=i.1; let W(p:Calendar)(i:Ω):= True; have hz' (p i)(h:W p i): Access K N p (z p i):=
    ⟨_,i.2.1.property,_,i.2.2.1.property,rfl⟩
 let A0(p:Calendar)(i:Ω):= constantCrop X (-Real.log p.2) hd he (x i) (y i) k (t p.1)
 let Δ(p:Calendar)(i:Ω):= today F J (d:=d) (e:=e) (V p i) (χ i) p.1 (p.1*p.2) p.1 (x i) (y i)-A0 p i
 have hp (u:AppointedH140Inputs G d)(w:AppointedH140Inputs G e): Sold P∥ W (fun p _=>Δlog p) (fun p _=>o p) (fun p i=> Δ p i u w):= by
   apply Fork.Sold.price (pays_form F J R Z M ν H hK hx hN hz t ht hμ hX hY hQ hU hB k hV hv hw hw' ha hz'
      (repack (GradedFar.raised hd u) (GradedFar.raised he w)) V)
   filter_upwards [Road.funded_forms hK hx hN hz hz',poses (show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin),
      ifWide,poses (eventually_all.mpr H₁), poses (eventually_all.mpr H₂)] with p hr he' hv hj hk i hi
   specialize hr i hi; change ‖today F J (V p i) (χ i) p.1 (p.1*p.2) p.1 (x i) (y i) u w - A0 p i u w‖ ≤ _; unfold A0
   rw [today_pack F J u w (V p i) (χ i) he' hr hj hk, pack_series X hd he u w hr (zero_lt_one.trans_le hv.1)]
 have hc:Safe P∥ W (fun p _=> Δlog p) (fun p _=>o p):= Road.log_safety ((poses (strength_positive hG)).mono (fun p hr i _=>pow_nonneg hr.le _))
 let u(i:Ω):=i.2.2.2.2.1.val; let v(i:Ω):=i.2.2.2.2.2.val
 have hs (a:Picks G d): Sold P∥ W (fun p _=>Δlog p) (fun _ _=>1) (fun p i=> multipliers (u i) a):=
    Fork.Sold.bounded (c:=1) zero_le_one (Eventually.of_forall fun p i _=> by simpa only [one_pow,mul_one] using multipliers_le zero_le_one (u i) a (i.2.2.2.2.1.property))
 have hs' (a:Picks G e): Sold P∥ W (fun p _=>Δlog p) (fun _ _=>1) (fun p i=> multipliers (v i) a):=
    Fork.Sold.bounded (c:=1) zero_le_one (Eventually.of_forall fun p i _=> by simpa only [one_pow,mul_one] using multipliers_le zero_le_one (v i) a (i.2.2.2.2.2.property))
 have hQ: Sold P∥ W (fun p _=>Δlog p) (fun p _=>o p) (fun p i=> Δ p i (u i) (v i)):= by
   simp_rw [expand_both (Δ _ _) (u _) (v _)]; refine Fork.Sold.sum hc (fun i _=>?_)
   have hv (j:Picks G e): Sold P∥ W (fun p _=>Δlog p) (fun p _=>o p) (fun p a=> multipliers (v a) j*Δ p a (basisWord i) (basisWord j)):=by
     simpa only [one_mul] using Fork.Sold.mul hc (hp (basisWord i) (basisWord j)) (hs' j)
   simpa only [one_mul] using Fork.Sold.mul hc (Fork.Sold.sum hc (fun a (_:a∈Finset.univ)=> hv a)) (hs i)
 obtain ⟨j,b,hb,H'⟩:= hQ; obtain ⟨T,hT,HT⟩:= physicalOnsets.mp H'
 refine ⟨ b,hb,j,T,hT,?_⟩; filter_upwards [HT] with r hr T' ht hh x hX y hy o ν u v hu hv
 specialize hr T' ht ⟨(show 1≤T by linarith only [hT]).trans ht,hh⟩ ((ν,⟨x,hX⟩,⟨y,hy⟩,o,⟨u,hu⟩,⟨v,hv⟩):Ω) trivial
 exact hr.trans_eq (mul_right_comm _ _ _)
end YM.Integration.GradedFar.Tariff.Crosser
