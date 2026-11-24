import YM.QuadraticLocal.Cycle.Cap
/-! # Don't CHARGE the whole spray.Buy with an authentic polynomial-Reserve cost

Reserve argument may be an order in moving stage growth.Any wanted
 exponent is admissible by schedule. In final short-program progression
 take `B_t = min (spray) (β^wanted)` as a cruder upper estimate only,
 after publishing with this ledger (including for restoring from real path prices).
 This section defines the actual cost operation. Parameterized by all voter data:
 to compare driven Φ or vacuum choices need the appropriate re-expression
 receipts still. Purchased with all moments, height covariance path model budgets
 independently demonstrated, calendar seller still invoked before using on all θ.We.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.MintClock
open Function Filter Finset Lattice RG Pressure Ac Marker Next.Scheduling
open Wilson RG.Supply PhysicalNext Repeat
open ConnectedActivityE6 Push Push.AbsoluteSums Coat RemainderComparison
open AnalyticBridge VerifiedReset QuadraticLocal.Earn QuadraticLocal.Mentor Animals
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Page
variable (G:Gauge)(D:Side)(P:Page)(U V:Stage)
variable (hP:Eligible G D P) (x:ℝ)
local notation "K"=> (fun x=> Pressure.betaF G x D)
local notation "Q"=> Delay.fineMonitor G D
local notation "D'"=> D.val
local notation "Bu"=> radiusB x
local notation "Bf" => radiusB ( K x )
local notation "C"=> U.supportExponent
local notation "a"=> V.supportExponent+1+1
local notation "ψ"=> (P.computes G D x)
-- NO absolute sum crossing q-world to another. For comparison norm p.B arcs.
noncomputable def beam := 4 ⊔ (tariff G D P U x C (P.a/4) Bf ⊔ tariff G D P V x (a) (P.b/4) Bu) ⊔ (P.raising D x ⊔ P.supervisor x ⊔ P.payroll x) ⊔ ( Page.life D P V x ⊔ Page.flow P V x ⊔ Spire.fees D (a) ⊔ (Willow.haloSlack Bu)⁻¹ )
local notation "Y"=> beam G D P U V
variable {u:ℝ}
lemma roofers : 4≤Page.beam G D P U V x:= le_sup_left.trans (le_sup_left.trans le_sup_left)
variable {p q:BudgetPoint}
lemma season_fee (h:Time.Same U p)(ht:Time.Same V q)(hp:p.B=Bf)(hq:q.B=Bu): Y x ≤ u ↔ 4≤ u∧ (ψ).inFee G p ≤u ∧ (ψ).outFee G q ≤u ∧ (ψ).produce D ≤u∧ (ψ).supervisor ≤ u ∧ (ψ).payroll ≤u∧(ψ).school D q≤u∧ (ψ).flow q≤u∧ Earnings.past D q≤u∧ (Willow.haloSlack q.B)⁻¹≤u:=by
    have he : (ψ).inFee G p=tariff G D P U x C (P.a/4) Bf:=by change Invoice.price p _ _ _ _ _ _=_; rw [h.2.2]; exact front_quote G D P U x h _ hp _ _
    have hz : (ψ).outFee G q=tariff G D P V x (a) (P.b/4) Bu:=by change Invoice.price q _ _ _ _ _ _=_; rw [ht.2.2]; exact front_quote G D P V x ht _ hq _ _
    obtain ⟨hx,hF,hT⟩:= Page.template G D P V x ht; rw [he,hz,hx,hF,hT,hq]; unfold beam; simp only [sup_le_iff]; dsimp only [computes, Earnings.produce,Page.raising]; tauto
-- full reserve, even if only bought under larger clock caps at some x. Positive growth comparison everywhere.
private lemma riseMax (g h:ℝ→ℝ)(hf:Reserve G D g)(hh:Reserve G D h):Reserve G D fun x=> g x ⊔ h x:=by
 apply (hf.absolute.add hh.absolute).compare; filter_upwards with x
 rcases le_total (g x) (h x) with h|h;
 · rw [sup_eq_right.mpr h]; exact (le_add_of_nonneg_left (abs_nonneg _)).trans (le_abs_self (_+_))
 rw [sup_eq_left.mpr h]; exact (le_add_of_nonneg_right (abs_nonneg _)).trans (le_abs_self (_+_))
include hP
lemma beam_res : Reserve G D (beam G D P U V):=by
    let h(g h:ℝ→ℝ) (ha:Reserve G D g) (hv:Reserve G D h):= riseMax G D g h ha hv
    exact h _ _ ( h _ _ (h _ _ (Reserve.const _) (h _ _ (Page.income G D P U Page.f_res C _) (Page.income G D P V Reserve.field (a) _))) (h _ _ (h _ _ (Page.proceeds G D P hP) hP.swept) hP.offered)) (h _ _ (h _ _ (h _ _ (Page.tons ..) (Page.movement ..)) (Reserve.const _)) (Page.season ..)) -- `def` lambda inside Bf syntax reused x.Power Member
omit hP
variable (g:ℝ)
-- convert FUTURE stamp charge. Full Campus shape from this point.Hall.Valid at new growth number. reserve (min survey not charged).
lemma drops (h:Time.Same U p)(ht:Time.Same V q)(hp:p.B=Bf)(hq:q.B=Bu)(he:Earnings.Cashier (P.computes G D x) G D p q u (Willow.haloSlack (radiusB x)) g): (Y x ≤ u) ∧ Earnings.Cashier (P.computes G D x) G D p q ( Page.beam G D P U V x ) (Willow.haloSlack (radiusB x)) g:=by
 let v:= Page.beam G D P U V x; let hh:= he.reserve; have hv:0<v:= by linarith only [show 4≤v from roofers G D P U V x ]
 obtain ⟨h',hC,hX,hY,hE,hA,hF,hv₁,hB,hb⟩:= (season_fee G D P U V x h ht hp hq).mp (le_refl v)
 constructor
 · apply (season_fee G D P U V x h ht hp hq).2; rw [hq]; refine ⟨he.strong,he.wage, he.quote, he.earns, he.director, he.manages,he.near,he.velocity,he.passGap,(inv_anti₀ (inv_pos.mpr he.paysAbove) he.reserve).trans_eq (inv_inv _)⟩
 rw [hq] at hb; exact ⟨h',hC,hX,hY,he.past_small,he.breeze,he.soon,he.price,he.shape,he.schedule,he.tenor,he.fame,hE,hA,hF,hv₁,hB,(inv_anti₀ (inv_pos.mpr (Willow.spare_pos _)) hb).trans_eq (inv_inv _)⟩
end Page
end YM.QuadraticLocal.MintClock
