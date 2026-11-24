import YM.AllOrder.Quay.Thaw
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Quay
open Function Filter Work Tensor Lattice Wilson RG Ovens Finset
open WilsonStartup WilsonStartup.Design WilsonStartup.Start WilsonStartup.Padded Floe Floe.Crest Till Tilt Burn
open PhysicalNext Repeat Pressure ConnectedActivityE6 ConnectedActivityE6.Coat Rosary
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
variable {κ j k a c : ℕ}{σ ω' α T C:ℝ}
variable (p:BudgetPoint)(h:Clip)(β:ℝ)
section
open Real (exp log)
open RG.Shoot Progress.DirectedRecipe Payments
open AnalyticBridge VerifiedReset
local notation "M"=>Timing.M
local notation "N"=>Timing.normK
-- to One post.Ok
structure Weather (G:Gauge)(S:Stage)(k:ℕ)(p:BudgetPoint) (β x:ℝ):Prop where
    margin : p.threshold ≤ permit G (horizon k) S.order S.power
    ticket : Burn.Capacity G p x k
    books : Real.exp p.supportExponent*costFace (|Start.weight S.clip β| *perCost p (horizon k) G) ≤ young x k
    pin :∃ s κ γ:ℝ,Loan p (x/2) s κ γ∧ Payments.Rates p.B (Timing.normK (Real.log x)) (coupon κ γ) (wad p (|Start.weight S.clip β| *item G p)) (κ-1)
    silver : silver x+young x k ≤ x^(-(11/10):ℝ)
def BandTar (G:Gauge)(S:Stage)(k:ℕ)(t:ℝ): Prop:= ∀ p:BudgetPoint,p.threshold=Pressure.temp t → p.B=radiusB t → Time.Same S p→ ∀ β,Decent S.clip p → t/2 ≤ β→ β≤ 2*t → Weather G S k p β t
lemma coins (x y:ℝ)(h:x≤y): costFace x≤ costFace y:= by unfold costFace; gcongr
lemma slotW (x y:ℝ)(h:x≤y): wad p x ≤ wad p y:= by apply coins; gcongr
-- prices
variable (S:Stage) (k)
set_option quotPrecheck false
local notation "Ω"=> (credit k)
local notation "b"=> (k)
local notation "l"=>horizon k
include S
lemma thaw:∀ᶠ x:ℝ in atTop, BandTar G S k x:= by
 have ht := prayer (G:=G) k S.order S.power; have hV: Rate G trivialL (Ω-1/80) (fun x=> Real.exp S.supportExponent*costFace (pricee G (l) S.order S.power x)):= ((ht.mul_left _).mul_left _)
 have h₀:Rate G trivialL (-(7/5)) (fun x=>silver x+young x k):=(tracks G _).add ((tracks G _).weaken (by unfold credit alt extraN; push_cast; linarith [show 0≤(k:ℝ) from Nat.cast_nonneg k] : Ω≤ -(7/5:ℝ)))
 let ξ := log ; let p₁:=Start.price G S.order S.power; let y:= permit G (horizon k) S.order S.power; have hz := (minted G (horizon k) S.order S.power).2
 filter_upwards [eventually_gt_atTop (0:ℝ),(temp_rate (G:=G)).below (by norm_num) _ hz,Burn.worth G k S, hV Ω (by linarith), Real.tendsto_log_atTop.eventually (nearly), Real.tendsto_log_atTop.eventually (Timing.growing.eventually_ge_atTop 1), Real.tendsto_log_atTop.eventually (Timing.loan S.supportExponent), (cartwork (G:=G) S).below (by norm_num) (1/4) (by norm_num), h₀ (-(11/10:ℝ)) (by norm_num)] with i hi hy hC hΩ he hv hl hw hr p ht hB hp β hd hb hb'
 let k':= M (ξ i); let γ:=Timing.quota (ξ i); have hA:Start.Loan p (i/2) k' k' γ:=by rw [← Real.exp_log hi]; simpa only [Real.exp_log hi] using (show Loan p (exp (log i)/2) k' k' γ from hl p (ht.trans (tempS hi)) hB hp.2.2|>.1) -- cannot rw ←exp_log because in k' depends let? fine.inspect
 let d₀ := |Start.weight S.clip β|; have h₁:0≤β:=le_trans (by positivity : 0 ≤ i/2) hb; have hj: d₀ ≤ 2*i:=by rw [←Real.norm_of_nonneg h₁] at hb'; exact (Start.weight_le β hd.direct).trans hb' -- rew rhs hb? ← Real.norm .. β needed
 have hh:0≤ d₀:=abs_nonneg _; let f:= d₀*item G p; let c:= wad p f; have hF:0≤ f:=mul_nonneg hh (item_pos _ _).le; have h0:0≤ c:=by unfold c wad costFace; positivity
 rw [hat_this] at hr hΩ; refine ⟨?_,hC _ ht hB hp.2.2 hp.2.1 hp.1, ?_, ⟨k',k',γ,hA, kernel_currency p (log i) he hv hA rfl h0 ?_ ⟩, (le_abs_self _).trans hr⟩
 · rw [ht]; exact (le_abs_self _).trans hy
 · unfold young; refine le_trans ?_ ((le_abs_self _).trans hΩ); let a:=gold G l p.order p.power; have hz: 0≤ perCost p l G:=by unfold perCost; have hm:= (minted G l p.order p.power).1; have he:= p.threshold_pos; positivity
   apply le_trans (mul_le_mul_of_nonneg_left (coins _ _ (mul_le_mul_of_nonneg_right hj hz)) (Real.exp_pos _).le); unfold pricee perCost; rw [ht,hp.1,hp.2.1,hp.2.2] -- hp reversed?
 · refine le_trans ?_ ((le_abs_self _).trans hw); let r:=item G p; have ht: r≥0:= (item_pos _ _).le; apply le_trans (mul_le_mul_of_nonneg_left (slotW p _ _ (mul_le_mul_of_nonneg_right hj ht)) (by positivity)); unfold wad scarfE crownE countH scarf r item; rw [hB,‹p.threshold=Pressure.temp i›,hp.1,hp.2.1,hp.2.2]
-- timetable for Pad using p.Partner and Boot. ∀ upper Norm common.
end
end YM.AllOrder.Quay
