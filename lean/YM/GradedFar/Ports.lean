import YM.GradedFar.Snap
import YM.GradedFar.Pan
/-!
# Preinverse measurements of RoundMeter authenticated budgets

Uniform length prices; paired tails per those installations. Receding geometry, M.3 authenticated pulse for `m_N`
constant-reference version of actual (uncropped) cutoff moment. Can compare at unrounded points to both S-none and predictions. Packet
cost uses (already shown) continuum comparison, no estimation of m_N derivatives. This
budget is a consequence of earlier results, not requisite for inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h l p k :ℕ}{K:Set (Points n)}{N:Set (Points m)} {U B a η:ℝ}
local notation "g∴"=> strength G
local notation "Γx"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "X♯"=> GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "S•"=> moving G U B
local notation "Y₁"=> atLength F P
local notation "D₁"=> atCenter F P h
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
    (hQ:FullVolume.FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)
variable {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)
-- price at any exterior shape Y. ensure BUY simultaneously for both center and full true estimators. TV additional. For cutoff center rows can take precisely zero rounded center.
def RoundedWell (C:Family G)(p:ℕ)(x:Points n)(y:Points m)(r T:ℝ)(z:Positions n)(z':Positions m)(L:ℝ): Prop:=
    ‖rounded C r p (Fin.append z z')-forest x (T•y)‖ ≤ L ∧
    ‖rounded C r p (Fin.append (0:Positions 1) z')-outgoing (T•y)‖ ≤ L
include H Ht hF Hq hK hx hN hz hU hB hQ hp hC ν hd he hh
private lemma priced (q:ℕ)(S':ℝ)(hv:0≤S'): ∃ b:ℝ,0≤b ∧ ∀ᶠ p in S•, ∀ᶠ i : ℕ×ℕ in (again f).fuse,
    Awarded (C:=C) (Fin.append d e) i.1 i.2 ∧ Awarded (C:=C) (Fin.append (Output h) e) i.1 i.2 ∧
    ∀ s:Lattice.Site (C.side i.1 i.2),∀ o x y, x∈K → y∈N → ∀ z z', RoundedWell C i.1 x y p.1 p.2 z z' (S'*g∴ p.1^(q+1))→
     ∀ (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u 1→ Box v 1→
        ‖recite F P p.1 (p.1*p.2) z z' s u v - atLength F P none o p.1 p.2 x y u v‖ ≤ b*g∴ p.1^q*p.2^(FVA2.GradedFar.power e) ∧
        rowPrice (pulseRow F P h p.1 (p.1*p.2) s z' v - D₁ none o p.1 p.2 y v)≤ b*g∴ p.1^q*p.2^(FVA2.GradedFar.power e) := by
 obtain ⟨b,hb,H'⟩:= front_sales F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz hQ hp hC hd he q S' hv
 obtain ⟨c,hc,HQ⟩:= front_sales F R J P Z M H ν Ht hF Hq hU hB isCompact_singleton little hN hz hQ hp hC (d:=Output h) (fun _=>hh) he q S' hv
 refine ⟨max b c,hb.trans (le_max_left ..),?_⟩; filter_upwards [H',HQ,ifWide,poses (strength_positive hG)] with p hp hv hT he
 have hi:(0:ℝ)≤p.2:= zero_le_one.trans hT.1; filter_upwards [hp,hv] with i hp hv
 refine ⟨hp.1,hv.1,fun z o x y hu₁ hu₂ q r hw u v h₁ h₂=> ?_⟩; constructor
 · exact (hp.2 z o x y hu₁ hu₂ q r hw.1 u v h₁ h₂).2.trans (by gcongr; exact le_max_left ..)
 apply row_pay (by positivity); intro w ht; rw [LinearMap.sub_apply,pulse_row,center_length F P]; exact (hv.2 z o 0 y (mem_singleton _) hu₂ 0 r hw.2 (fun _=>w) v ((boxes zero_le_one).mpr (fun _=>ht)) h₂).2.trans
    (by gcongr; exact le_max_right ..)
open Budget
variable (ha:0<a)
include ha
lemma mN_price (k:ℕ)(S':ℝ)(hc:0≤S'): ∀ᶠ q:ℕ in atTop, ∀ᶠ r in trail,∀ T:ℝ,receding (g∴ r) B a U T→∀ᶠ i in (again f).fuse,
    Awarded (C:=C) (Fin.append d e) i.1 i.2 ∧ Awarded (C:=C) (Fin.append (Output h) e) i.1 i.2 ∧
    ∀ s:Lattice.Site (C.side i.1 i.2),∀ o x y z z', x∈K→ y∈N→ RoundedWell C i.1 x y r T z z' (S'*g∴ r^(q+1))→
    ∀ u:AppointedH140Inputs G d,∀ v:AppointedH140Inputs G e, Box u 1→ Box v 1→
    ‖recite F P r (r*T) z z' s u v-Y₁ none o r T x y u v‖ ≤ g∴ r^k*T^(-(h:ℝ)-η) ∧
        rowPrice (pulseRow F P h r (r*T) s z' v - D₁ none o r T y v) ≤ g∴ r^k*T^(-(h:ℝ)-η):= by
 let p:= FVA2.GradedFar.power e; let m:= -(h:ℝ)-η; obtain ⟨A,hA⟩:= exists_nat_gt (B*(p-m)+k)
 filter_upwards [eventually_ge_atTop A] with q h; obtain ⟨b,hb,H⟩:= priced F R J P Z M H ν Ht hF Hq hU hB hK hx hN hz hQ hp hC hd he hh q S' hc
 obtain ⟨T,hT,H⟩:= physicalOnsets.mp H; let X:= strength_falls hG
 have hf:B*(p-m)<q-(k:ℝ):= by linarith [ (Nat.cast_le (α:=ℝ)).2 h]
 filter_upwards [H,X.eventually (trade hB ha hU b hb 0 hf), X.eventually (upwards hB ha T)] with
    r hr hf hup T' he; have ht':T≤T':=(hup _ he.1); have hp': 1≤T':= one_le_two.trans (hT.trans ht'); specialize hf T' he; rw [Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast, pow_zero,mul_one] at hf
 filter_upwards [hr T' ht' ⟨hp',he.2⟩] with p H
 exact ⟨ H.1,H.2.1,fun s o x y z z' h₁ h₂ he u v hu hv=> let ht:= H.2.2 s o x y h₁ h₂ z z' he u v hu hv; show _ from ⟨ht.1.trans hf,ht.2.trans hf⟩ ⟩
end YM.Integration.GradedFar.Auth
