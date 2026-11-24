import YM.AllOrder.Rosary.Puzzle
import YM.QuadraticLocal.Feast
/-!
# qlocal along reclosure (extending `AllOrder/Rosary/Puzzle` proof)

Using Frost future charged width; establish receipt for marked slips on same final representation.
Stack: local main. Mark use after generation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/-! Pole & Estimate budgets billed after L. Coarse T.cost=up betaHat(s) or down exactly (for simplicity). -/
namespace Repair
open Push PriceCompiler Floe Floe.Step Floe.StateE Floe.Step.PlanV Plateau PhysicalNext.Repeat Pressure
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Catch Catch.Clock -- maybe remove
open Tilt
-- Cost ratio for nearby betas. Payout via Search lease. Includes weighted difference with all mask.Finance.
local notation "Z"=>Real.exp
namespace PostP
open Guard Lapis Gyro Time Morning Ac
variable {A:Layout G} {q:ℕ}{β k u t Κ ℓ D a w':ℝ} (S:Stage) (Γ:Floe.Step.Fees)
    (hm:∀ i,0<Γ i)(he:Loft p n)(h:G.Simple)(hp:Decent S.clip p)(hv:Width (pearl p) S.clip S.width)
    (hQ: R.Bounds S.clip S.width S.paths Λ)(x:ℝ)(hx:0<x)
local notation "τ"=> Burn.horizon q
local notation "ℬ"=> Age.scope (τ+2)
local notation "W"=> S.width
local notation "C"=> S.paths
local notation "B"=> p.B
variable (h0 : Time.Same S p)(hB:p.B=radiusB x)(ht:p.threshold=temp x)(hA: ∀ i∈Age.scope (Burn.horizon q+2),Quoted (A i) (Γ i) (authority (Burn.horizon q) i (strengthP x)))
    (hA': 4*(Burn.horizon q+4)≤p.B)
local notation "L"=> θ1 G S x q
local notation "L₁"=> θ2 G S x q
local notation "∆"=> Averaging.delta
local notation "e"=> (C' p G q β x)
local notation "βp"=> (β+k)
variable {Ξ:Cane G n ι} [Countable ι] (hp':Ξ.Ready p (x^(-(2/5:ℝ))))
local notation "M₁"=> offerS G p A ℬ (gStep (β+k)) -- pred
local notation "R'"=> offerS G p A ℬ (gStep (β+k+a)) -- actual
local notation "E"=> err A B ℬ (gStep (β+k)) (gStep (β+k+a))
-- moment.Pre.Weight `aux α=k-u` old. FSmall statement.InputCap.M.Inv. Guards.Lume.K margin.Reuse Sunset.B.Workloads.Surface relations. Term exact all masks.
variable {X': Listing G n}{v':Collection.Source G n}{κ H':ℝ}
    (hX:Collection.Local X p v (θ1 G S x q) w)(hy:Collection.Local X' p v' H' w')


-- p prices.Local & eval.K.D.Provenance later. Compare only needs actual old early on parallel healthy. hXsup for error.Conservation FULL gate equality target.ALL U. after move if variant used need original β projection via Spin.
variable (hb : ∀ U:Config G n, flags p.threshold U=∅→ gate R S X v p (offerS G p A (Age.scope (Burn.horizon q+2)) (gStep (β+k))) Ξ k β ℓ U=earlyValue X' R S.clip p v' β t (k-u) U)
    (ha:a=delta (X'.read v')-u)
    (hk: ∀ i:Actor G S q H x, Checks G S q H i)
    (hr:Payments.Rates p.B D w (x^(-(1/3:ℝ))) Κ)
    (hs: Burn.Near x (β+k+a) ∧ Burn.Near x (β+k) ∧ |k| ≤ H ∧ |u| ≤ H ∧ H'≤x)
include S Γ hm he h hp hv hQ hx h0 hB ht hA hA' hp' hX hy hb ha hk hr hs

local notation "J"=> (∆ (X.read v)-a)
/-- Deliver masked horizon estimate. Ξ paid soft.Frozen ledger with error β relative exact model.K meets.Also η adjustment be used on α'. -/
theorem feast_ride {y₀:ℝ} (hy₀:0≤y₀) (hY:Payments.Rates p.B D w ((x^(-(1/3:ℝ)))+y₀) Κ) : p.threshold^2* |a| ≤ θ2 G S x q∧∃ (V:Pipes G n)(K':Tap G n), Ingredients V K' p (beg x/32) D ∧ Nonempty (QuadraticLocal.Kiosk.Second p (X.read v) (finish R S.clip p V K' (β+k+a) (vac v ℓ)).activities w D p.supportExponent y₀) ∧ ∃ T: Seed (finish R S.clip p V K' (β+k+a) (vac v ℓ)) R', Candor p ((finish R S.clip p V K' (β+k+a) (vac v ℓ)).activities) (Set.range T.model) (silver x) (young x q) ∧ ∀ U, (finish R S.clip p V K' (β+k+a) (vac v ℓ)).eval U=gate R S X v p M₁ Ξ k β ℓ U:= by
 obtain ⟨hδ,hδ',hbK,hW,hH⟩:=hs; let z:= s_p x
 have h0': ∀ i∈ℬ, 4*i.r ≤ B := fun i hi=> le_trans (Nat.mul_le_mul_left 4 (i.pricey.trans ((Nat.add_le_add_right (Age.in_scope.mp hi) 2).trans (le_of_eq (by omega))))) hA'
 let hP (d:ℝ)(x':Site n): Fairness p x' (court x' p.B) (offerS G p A ℬ (gStep d) n x') (C' p G q d x):= Tilt.paint _ _ _ Γ hA h _ _ (by have hV:=he.roomy; omega) _ _ hm h0'
 let hℓ:= hP (βp); have hσ: PhysicalNext.Repeat.Trio.Mirrors ((M₁) n):= Tilt.signed _ _ _ _ n
 have hg: |J|≤ reward n p.threshold* vault n p (Guard.totalFee p G S.clip S.width S.paths k u (C' p G q (β+k) x) L + H'):=by
    rw [show J= Averaging.delta (X.read v)+u-Averaging.delta (X'.read v') from (by rw [ha]; ring)]; refine Guard.gauge_cost hQ hp hv he.roomy h u k M₁ hℓ hσ hX hy ℓ (β:=β) (ℓ':=t) (fun U h=>?_); rw [← hb U h,gate, tsum_congr (show ∀ i, Ξ.values i U=0 from fun i=> by_contra fun he=> (hp'.2.1 i).2.2.2 U he (by simp [Healthy,h])), tsum_zero, Real.exp_zero, mul_one] -- syntax
 let Z':= ∆ (X.read v); have heq : β+k+a- (β+k)= a:= (by ring); let A':Actor G S q H x:= ⟨p, ⟨h0,hB,ht⟩, n, he,β+k+a,β+k,k,u,J, Z', H',⟨hδ,hδ',hbK,hW,Collection.Local.H_nonneg hy,hH⟩,(by rw [heq]),delta_bound h hX.projects,hg⟩; let hK:=hk A'; have he': p.threshold^2* |a| ≤ θ2 G S x q:= heq ▸ (show p.threshold^2* |β+k+a-(β+k)| ≤ _ from hK.reset); refine ⟨he',?_⟩;
 obtain ⟨s⟩:= Signal.in_time n he.roomy p; let y:=θ2 G S x q; let b:= C' p G q (β+k+a) x; let z':=taxes p G q (β+k) (β+k+a) x; let Y' := Lapis.flare G n p J+(x^(-(2/5:ℝ))+softNeed G p S.clip S.width S.paths k y); have hw: Collection.Local X p v y w:= by
    obtain ⟨f,hH,H₁⟩:= hX.cheap; exact {hX with cheap:=⟨f,hH,fun i=> Extra.Iteration.Cost.enlarge (H₁ i) (show θ1 G S x q ≤ 2*θ1 G S x q from le_mul_of_one_le_left (hX.H_nonneg) (by norm_num))⟩}
 have hwidth : Width p S.clip S.width:=⟨hv.1,hv.2.1,(div_le_div_of_nonneg_right (show p.supportExponent+1≤(pearl p).supportExponent+1 from (by unfold pearl preExponent; dsimp; linarith)) (Nat.cast_nonneg p.B)).trans hv.2.2⟩
 have hz : 0 ≤ Y':= by
    have hZ := (go s (J) h hp.radius).2; obtain ⟨u,H',hθ⟩:=hZ.2.2; have h0:0 ≤ Lapis.flare G n p J:= Push.AbsoluteSums.budget_nonneg (hθ 0)
    obtain ⟨-,v',-, -,hσ⟩:= (Morning.base0 Ξ k a S.paths Λ (x^(-(2/5:ℝ))) h hp hw hQ he.roomy hwidth hp' he' |>.2.2); have he':0 ≤ softNeed G p S.clip S.width S.paths k y:= AbsoluteSums.budget_nonneg (hσ.2 0); unfold Y'; positivity
 let hy(x':Site n) : Fairness p x' (court x' p.B) (E n x') z':= repairs A Γ hm (gStep (β+k)) (gStep (β+k+a)) (strengthP x) τ ℬ hA h x' (by have h:=he.roomy; omega) h0' -- type .. before explicit
 obtain ⟨V,t,hV,hD,T',hS,hT⟩ := ready_pass (μ:=D) Ξ s k a R' E S.paths b z' Λ (W':=Κ) (x^(-(2/5:ℝ))) h hp hw hQ he.roomy hwidth hp' he' (hP (β+k+a)) hy (Tilt.signed _ _ _ _ n) (Tilt.signed _ _ _ _ n) (Tilt.regional _ _ _ _) β ℓ (hedge_ok hr hr.hard le_rfl hz hK.kernel le_rfl) (hedge_ok hY hr.hard le_rfl (add_nonneg hz hy₀) (add_le_add (show Y'≤ x^(-(1/3:ℝ)) from hK.kernel) le_rfl) le_rfl)
 let r0:= Real.exp p.supportExponent*z'+(food G n p J+ regularNeed G p S.clip S.width S.paths 0 y); let r:= finish R S.clip p V t (β+k+a) (vac v ℓ); have hh: r0 ≤ young x q:= hK.economies
 refine ⟨V,t,VerifiedReset.Use.compatible_ingredients hV ((add_le_add hK.worth hK.economies).trans hK.funded) le_rfl,hD,T', hS.loosen (R:=r) hK.worth hh,fun U=>?_⟩; rw [hT]; unfold truth gate portal; let A' := ∑' i, Ξ.values i U; rw [mul_assoc, ← Real.exp_add]; congr 2; rw [show news (offerS G p A ℬ (gStep (β+k+a))) p U+ news (E) p U =news (M₁) p U from ?_]; abel
 unfold news; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; let εo:= court i p.B; by_cases hf : Healthy p.threshold εo U; · rw [masked_eq _ _ _ _ hf,masked_eq _ _ _ _ hf,masked_eq _ _ _ _ hf]; rw [Repair.pure]; simp
 rw [masked_ne _ _ _ _ hf,masked_ne _ _ _ _ hf,masked_ne _ _ _ _ hf]; ring
end PostP
end Repair
end YM.AllOrder.Rosary
