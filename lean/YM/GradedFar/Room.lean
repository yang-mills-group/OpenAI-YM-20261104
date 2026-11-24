import YM.GradedFar.Lay
import YM.GradedFar.Stair
/-!
# Common 'eventual' of moving interval. Price estimates not changing horizon/general quantities.

Don't confuse with product/Cursor 'iterated' filter. Uses `prod` and filter on Wide,
yields right-sided and correct `T₀` usual for the interval.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Tariff
open Function Filter Set PowerSeries
open Climb Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh Neighbor
open Fork (Setting Sold)
open scoped Topology BigOperators Classical
variable {G:Gauge}

abbrev Calendar := ℝ×ℝ -- (r,T)
def Δlog (p:Calendar):=1+Real.log p.2
def wallet (G:Gauge)(p:Calendar):= (strength G p.1)⁻¹

def moving (G:Gauge)(U B:ℝ): Filter Calendar := (trail ×ˢ atTop) ⊓ Filter.principal {p|Wide G U B p.1 p.2}
variable {U B:ℝ}{P:Calendar→Prop}
local notation "u"=> moving G U B
local notation "g"=> strength G
lemma physicalOnsets : (∀ᶠ p in u,P p) ↔ ∃ T₀:ℝ,2 ≤ T₀ ∧ ∀ᶠ r in trail,∀ T:ℝ,T₀≤T → Wide G U B r T → P (r,T):=by
 rw [moving,eventually_inf_principal]; constructor
 · intro h; obtain ⟨a,ha,b,hb,h⟩:= Filter.mem_prod_iff.mp h; obtain ⟨x,hx⟩:= eventually_atTop.mp hb
   exact ⟨max 2 x,le_max_left ..,(show ∀ᶠ r in trail,r∈a from ha).mono fun r hr t ht=> h (show (r,t)∈a ×ˢ b from ⟨hr,hx _ ((le_max_right ..).trans ht)⟩)⟩
 rintro ⟨T₀,h₀,h⟩; exact mem_of_superset (Filter.prod_mem_prod h (eventually_ge_atTop T₀)) (fun p h hp=> h.1 p.2 h.2 hp)
lemma poses {h:ℝ→Prop}(hh:∀ᶠ r in trail,h r) : ∀ᶠ p:Calendar in u, h p.1:= physicalOnsets.mpr
    ⟨2,le_rfl, hh.mono (fun _ hr _ _ _=>hr)⟩
lemma horizonUp {h:ℝ→Prop}(hh:∀ᶠ T in atTop,h T): ∀ᶠ p:Calendar in u,h p.2:=by
 obtain ⟨x,hx⟩:= eventually_atTop.mp hh; exact physicalOnsets.mpr ⟨max 2 x,le_max_left ..,Eventually.of_forall
   fun _ t ht _=> hx t ((le_max_right ..).trans ht)⟩
lemma ifWide : ∀ᶠ p:Calendar in u, Wide G U B p.1 p.2:= physicalOnsets.mpr ⟨2,le_rfl,Eventually.of_forall fun _ _ _ h=>h⟩
lemma moneySafe : ∀ᶠ p:Calendar in u,1 ≤ Δlog p:= ifWide.mono (fun _ h=> le_add_of_nonneg_right (Real.log_nonneg h.1))
lemma rising : Tendsto Prod.fst u trail:= tendsto_def.mpr fun _ ha=>poses ha
lemma upward : Tendsto Prod.snd u atTop:= tendsto_def.mpr fun _ ha=> horizonUp ha
variable {hG:G.Simple}
include hG
lemma bring : ∀ᶠ p:Calendar in u,1 ≤ wallet G p := by
 filter_upwards [poses (strength_positive hG), poses ((Coupling.conforms hG (strength_coupling hG)).eventually_le_const zero_lt_one)] with p hp hc
 exact (one_le_inv₀ hp).mpr hc

lemma refee {Iota:Type*}{E:Type*}[NormedAddCommGroup E]{K:Calendar→Iota→Prop}{W:Calendar→Iota→ℝ}{f:Calendar→Iota→E}
    (hU:0<U)(hB:0<B)(hw:∀ᶠ i in u,∀ t,K i t→0≤W i t)(hf:Sold u K (fun i _=>Δlog i) W f): Sold u K (fun i _=>wallet G i) W f := by
 obtain ⟨k,b,hb,H⟩:= hf; refine ⟨1,b,hb,?_⟩
 filter_upwards [hw,H, ifWide, poses (pay_log (hG:=hG) hU hB k), poses (strength_positive hG)] with p hr hp hv hx he z h
 refine (hp z h).trans ?_; rw [pow_one]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
   (by rw [wallet,←one_div]; exact (le_div_iff₀ he).2 (hx _ hv)) hb) (hr _ h)
lemma rpow_paid (D:ℝ): ∀ᶠ k:ℕ in atTop, ∀ᶠ p:Calendar in u,(g p.1)^(-D) ≤ wallet G p^k:=by
 obtain ⟨k,hk⟩:= exists_nat_gt D; filter_upwards [eventually_ge_atTop k] with i hi
 filter_upwards [poses (strength_positive hG),bring (hG:=hG)] with p hp hb
 rw [Real.rpow_neg hp.le, ← Real.inv_rpow hp.le, wallet, ← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hb
   (hk.le.trans (Nat.cast_le.mpr hi))
lemma flatCost (hU:0<U)(hB:0<B)(j i:ℕ): ∀ᶠ p:Calendar in u,
    wallet G p^i*(p.1*p.2) ≤ g p.1^j:=by
 -- buy r ≤ g^K
 obtain ⟨k,hk⟩:= (Neighbor.spent (hG:=hG) hU hB (j+i) 1).exists; specialize hk 1 zero_le_one
 filter_upwards [poses hk, poses (radius_falls hG k), poses (strength_positive hG), ifWide] with p hP hc hG hv
 specialize hP _ hv; rw [one_mul,pow_one,mul_comm,pow_add] at hP; unfold wallet; rw [inv_pow,inv_mul_le_iff₀ (by positivity : 0 < g p.1^i)]
 exact (mul_le_mul_of_nonneg_right hc (zero_le_one.trans hv.1)).trans (hP.trans_eq (mul_comm ..))
omit hG
lemma Dirty.upper {n m:ℕ}{K:Set (Points n)}{S:Set (Points m)}(hK:IsCompact K)(hx:K⊆conf n)(hS:IsCompact S)(hy:S⊆Outside m):
    ∀ᶠ p:Calendar in u,∀ x∈K,∀ y∈S,forest x (p.2 • y) ∈ conf (n+m):= by
 -- use profile clearance
 refine horizonUp (h:=fun t=>∀ x∈K,∀ y∈S,forest x (t • y)∈conf (n+m)) ?_; filter_upwards [Real.tendsto_log_atTop.eventually (layout_eventually hK hx hS hy), eventually_gt_atTop (0:ℝ)] with r hr hp x hxx y hyy; simpa only [squeeze,neg_neg,Real.exp_log hp] using (hr x hxx y hyy).1
end YM.Integration.GradedFar.Tariff
