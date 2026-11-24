import YM.QuadraticLocal.Rebirth.Route
import YM.QuadraticLocal.Union.Commit
/-!
# Authorize the power currency. Reserve calendar price at this same Epoch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Rebirth
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open PositionX.Jet Extra.Iteration
open AllOrder AllOrder.Catch AllOrder.Catch.Clock AllOrder.Wheel AllOrder.Transit
open AllOrder.Rosary.Repair PostP AllOrder.Wheel.Ride
open Coat Next.Scheduling Next.Scheduling.Clock AllOrder.Floe
open Step Step.PlanV
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G: Gauge} {X: Metals G}
variable (D:RG.Supply.Rolls X.p)(R: Roots (G:=G) X.p.profile X.K X.p.kernel)
variable (x y:ℕ)(hx:4≤ x) {k:ℕ}
set_option quotPrecheck false
local notation "ρ"=> (Burn.horizon k)
local notation "L"=> D.L x
local notation "H"=> (fun t=> betaF G t (D.L x))
local notation "B"=> X.p.profile y
local notation "F'" => ( fun ξ:ℝ=> Pair.Note D R x y hx (q:=k) ξ )
local notation "N" => ρ+2
local notation "E"=> Aux.fare G (D.L x)
local notation "Z₁"=> (E).stage F'
variable (F: Income D R x y hx (Burn.horizon k))
open RemainderComparison
namespace House
open ThroughLaunch Pane AllOrder.Ink AllOrder.Ink.Money Rebirth.Chart
local notation "I"=> Card D R x y hx ρ
local notation "Ξ" t:max=> strengthP (H t)
local notation "T"=> ( Predicted D R x y hx F )
abbrev priceRule : Card D R x y hx ρ → ℝ:= fun i=> i.self.paid
local notation "v"=> F.sustenance.due
local notation "σ"=> (House.priceRule D R x y hx (k:=k))
lemma duty (j:ℕ)(hp:j ≤ Burn.horizon k+2): ∃ n,Pace.Cost (priceRule D R x y hx) n (fun i=> F.issue i j):= by
    rcases j with _|j; · exact ⟨0,by simp_rw [show ∀ i:I,F.issue i 0=0 from fun i=>( F.sustenance.due i ).1]; apply Pace.Cost.fixed⟩
    rcases j with _|j; · exact ⟨0,by simp_rw [show ∀ i:I,F.issue i 1=0 from fun i=>( F.sustenance.due i ).2.1]; apply Pace.Cost.fixed⟩
    rcases j with _|j; · exact ⟨0, CreditF.down (freeC _ (abs_nonneg (cloak D x))) (U':=fun i=> |F.issue i 2|) (fun i=> by change |F.issue i 2| ≤ _; rw [(F.sustenance.due i).2.2]; exact i.self.bounded.trans (le_abs_self _)) (fun _=> abs_nonneg _)⟩
    exact ⟨_,F.sustenance.income j (by omega)⟩
lemma universe_fee : ∃ n,∀ j≤ Burn.horizon k+2,Pace.Cost (priceRule D R x y hx) n (fun i=> F.issue i j):= by
    -- finite family. Lean choose
    choose n hn using fun i:(Fin (N+1))=> House.duty D R x y hx F i.val (Nat.le_of_lt_succ i.isLt)
    let C:=∑ i:Fin ((Burn.horizon k+2)+1),n i; refine ⟨_,fun j hj=> (hn ⟨j,Nat.lt_succ_of_le hj⟩).up (show _ ≤ C from Finset.single_le_sum (f:=n) (fun _ _=>Nat.zero_le _) (Finset.mem_univ _))⟩

abbrev grammar (M:ℕ) := ( Icc (-(M:ℤ)) (M:ℤ))
abbrev allot (M:ℕ) (i:I):ℝ:= 1+ ∑ z∈ (grammar M), ∑ j∈ Finset.Iic (Burn.horizon k+2), |tariff (F.issue i) ((F.sustenance.due i).1) (Burn.horizon k+2) z j|
local notation "Λ"=> (House.allot D R x y hx F)
lemma backs (M:ℕ)(z:ℤ)(i:I)(hs:z∈grammar M)(n:ℕ)(hn:n≤Burn.horizon k+2): 1+|tariff (F.issue i) ((F.sustenance.due i).1) (Burn.horizon k+2) z n| ≤ Λ M i:= by
    unfold House.allot; apply add_le_add_right; exact ( Finset.single_le_sum (f:=fun j=> |tariff (F.issue i) ((F.sustenance.due i).1) (Burn.horizon k+2) z j| ) (fun _ _=>abs_nonneg _) (Finset.mem_Iic.mpr hn)).trans (Finset.single_le_sum (f:=fun z=> ∑ j∈ Finset.Iic (Burn.horizon k+2), |tariff (F.issue i) ((F.sustenance.due i).1) (Burn.horizon k+2) z j| ) (fun _ _=> Finset.sum_nonneg fun _ _=> abs_nonneg _) hs)
local notation "Φ" i:max z:max j:max=> ( |tariff (F.issue i) ((F.sustenance.due i).1) (Burn.horizon k+2) z j| )
lemma owned (M:ℕ) : ∃ n,Pace.Cost (priceRule D R x y hx) n (House.allot D R x y hx F M):=by
    obtain ⟨n,hn⟩:=universe_fee D R x y hx F; let c:=n*(Burn.horizon k+2); have hv z j (hj:j∈ Finset.Iic (Burn.horizon k+2)): CreditF σ c (fun i=> Φ i z j):=by
       have ht:= Finset.mem_Iic.mp hj; exact ( Chart.restatement (Burn.horizon k+2) z σ (F.issue) (fun i=>(F.sustenance.due i).1) hn _ ht).up (by unfold c; nlinarith only [ht]) -- order args
    have he:CreditF σ c ( Λ M ):= ((freeC _ zero_le_one).up (Nat.zero_le _)).add (CreditF.sum (grammar M) (fun z _=> CreditF.sum (Finset.Iic (Burn.horizon k+2)) (hv z)))
    refine ⟨c,?_⟩; unfold Pace.Cost; simp_rw [abs_of_nonneg (he.nonneg _)]; exact he

abbrev amount (M:ℕ)(t:ℝ) : ℝ:= ((owned D R x y hx F M).choose_spec.choose+1)* (1+|strengthP (H t)|)^ ( (owned D R x y hx F M).choose )
local notation "Z"=> (House.amount D R x y hx F)
lemma serene (M:ℕ)(t:ℝ):1≤ Z M t:= by
    have hp:0≤ (owned D R x y hx F M).choose_spec.choose:=(owned D R x y hx F M).choose_spec.choose_spec.1; exact one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left hp) (one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _)))
lemma budgets (M:ℕ) : Reserve G L (House.amount D R x y hx F M):= by
    have he:Reserve G L (fun t=> strengthP (betaF G t L)):= (Reserve.const 2).mul Reserve.monitoring; exact (Reserve.const _).mul (((Reserve.const _).add he.absolute).pow _)
lemma settles (t:ℝ) (i : T t) (z : ℤ) (M:ℕ)(n:ℕ)(hn:n≤Burn.horizon k+2)(he:z∈ grammar M):1+ |tariff (F.issue i.news.token) ((F.sustenance.due i.news.token).1) (Burn.horizon k+2) z n| ≤ House.amount D R x y hx F M t:= by
    let h:= (owned D R x y hx F M).choose_spec.choose_spec.2 i.news.token; refine (backs D R x y hx F M z i.news.token he n hn).trans ((le_abs_self _).trans (h.2.trans ?_)); unfold amount; change _* (1+|priceRule D R x y hx i.news.token|)^_ ≤ _; rw [show ( House.priceRule D R x y hx i.news.token )=strengthP (H t) from i.news.earns]; gcongr; exact le_add_of_nonneg_right zero_le_one -- gcongr often discharges
end House
end YM.QuadraticLocal.Rebirth
