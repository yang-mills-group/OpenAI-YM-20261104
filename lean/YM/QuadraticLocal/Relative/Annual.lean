import YM.QuadraticLocal.Class.HoursCost
import YM.QuadraticLocal.Qarry
/-!
# Credit facts on the close continuation. Costs on ALL positions permitted
 at these indices, same roof, age verified.Depending close length with chosen
 relative error factor. Here ε parameter in practical x^(ε) notation
 (βhat clock cost convention, not g; convert in Reports with all leases).

 `Ψ` unmarked sources used in Budget.hint.G., not quantified at this stage
 because it holds along ANY till Lens representation. No fixed-period witnesses in
 cost_k. CAN reuse Calendar stationarity proof.Be.Scope. Uses true Authority PaceCost.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent.Sycamore
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open PaceR
open AllOrder.Catch Mentor
variable {G : Gauge} (R:Run G)(g:G.Simple)
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "A" => R.alloy.B.a
variable {m i b k N:ℕ} {Q ε δ p q x y:ℝ} (hp : 0 < ε)(hP : ε ≤1/8)
variable (U:Syl.School k) (hQ : 0≤Q) (l N:ℕ)
local notation "Y"=> (Φ b)
local notation "M"=> U.order
local notation "E"=> (Sycamore.notice R b U ε)
local notation "τ"=> ( Sycamore.tol U ε )
local notation "τ'"=> ( Sycamore.tol U (ε/2) )


local notation "r"=> (roof R m b)
-- Attends S2 schedule, no initial w mortgage. After each step shrink once, can afford at most torch. Burn.year.Sensor_Frame.We.Store
abbrev fire (k:ℕ) :ℕ:= k+8
-- W inflation polynomial `battery^pieces`. attested for restoration.
abbrev torch (k:ℕ) :ℕ:=(fire k+10)*(k+3)
abbrev battery (R:Run G)(k i b:ℕ):= ( PaceR.roof R i b )^(fire k)
abbrev fare_R (R:Run G)(k i:ℕ):= ( budgetR R i )^( fire k )
local notation "u"=> (U.pieces)
local notation "bR" i:max=> (battery R u i b)
lemma charged {k:ℕ} : 1≤ battery R k i b:= one_le_pow₀ (roof_ge ..)
lemma fades : 1≤ fare_R R u i:= one_le_pow₀ (budget_pos ..)
lemma steps (he:i<b) : battery R u i b= fare_R R u i * battery R u (i+1) b:= by unfold battery fare_R; rw [ PaceR.roof_step R he,mul_pow ]
-- integer calculus
lemma funded_degree (k:ℕ) : fire k*k + max (6*k) (fire k) +2 ≤ torch k:= by
   rcases le_total (fire k) (6*k) with hp|hp
   · rw [max_eq_left hp]; unfold torch; nlinarith only [ Nat.zero_le (fire k), Nat.zero_le k ] -- expansion
   rw [max_eq_right hp]; unfold torch; nlinarith only [Nat.zero_le (fire k), Nat.zero_le k]
structure Session (m b d:ℕ)(k:ℕ)(H:Syl.School k) : Prop where
   owns : Attends R H ε m b d
   candles : ( PaceR.roof R m b )^( Sycamore.torch H.pieces ) ≤ (Φ b)^ ε
-- remove b₀ dummy
local notation "𝓒" => Session (ε:=ε) R
include U g hp hP hQ
lemma readyYear (d:ℕ) : ∀ᶠ b:ℕ in atTop,∀ m≤b,Close R l Q m b→ Session (ε:=ε) R m b d k U:=by
 filter_upwards [learners (Q:=Q) R g hp hP U hQ l d, PaceR.gives R g l (torch u) Q hQ ε hp] with b h hz m hm ht; exact ⟨h m hm ht,hz m m le_rfl hm ht⟩
omit g U hp hP hQ
include U
variable (d:ℕ) (Hh:Session (ε:=ε) R m b d k U)(h:m ≤ i)(he:i ≤ b)
include Hh h he
local notation "cA" i:max=> (bR i)^u
local notation "cF"=> fare_R R u i
local notation "Kp"=> ( Sycamore.life R i b U ε )
local notation "BR"=> (battery R u i b)^u
lemma scoreS2 {r₀:ℕ}(ht:r₀≤ max (6*u) (fire u)+2): BR*r^r₀ ≤ (Φ b)^ε:= by
    have h₀: 1 ≤ (r):= PaceR.roof_ge ..; have hv:1≤ bR i:= charged R; -- note cA notation max precedence 
    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hv) (pow_le_pow_left₀ (zero_le_one.trans ( PaceR.roof_ge .. )) (roof_longer R h he) (fire u)) _) (pow_nonneg (zero_le_one.trans h₀) r₀)).trans (le_trans ?_ Hh.candles); rw [← pow_mul, ← pow_add]; exact pow_le_pow_right₀ h₀ ((Nat.add_le_add_left ht _).trans (by simpa only [Nat.add_assoc] using Sycamore.funded_degree u))
lemma attendsS2 : BR * ( Kp ) ≤ notice R b U (2*ε):=by
    have hf:= PaceR.positive R b; have hX : notice R b U (2*ε) = (Φ b)^ε * notice R b U ε:= by rw [notice, show tol U (2*ε) = ε+tol U ε from (by unfold tol; linarith), Real.rpow_add hf]; -- RHS notice defeq
    rw [hX]; unfold life; rw [← mul_assoc];
    apply mul_le_mul_of_nonneg_right _ (behalf R U|>.le); refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans ( PaceR.roof_ge .. )) (roof_longer R h he) (bill U)) (pow_nonneg (zero_le_one.trans (charged R)) u : 0≤ BR)) ( scoreS2 R U d Hh h he ?_ ); unfold bill; have hk:= le_max_right (6*u) (fire u); dsimp only [fire] at hk ⊢; omega
lemma wax : BR ≤ (Φ b)^ε:= by exact le_trans (le_of_eq (show BR=BR*((r)^0) from (by rw [pow_zero,mul_one]))) (scoreS2 R U d Hh h he (Nat.zero_le _))
-- Atmospheric.restore to TRUE normalized K, receipt.F.Query.
include hP
lemma pads : BR*((r)^6)^u ≤ Φ b:= by
    rw [← pow_mul (r) 6]; exact (scoreS2 R U d Hh h he (Nat.le_trans ( le_max_left (6*u) (fire u) ) ( Nat.le_add_right .. ))).trans ((Real.rpow_le_rpow_of_exponent_le (show 1≤Φ b from (R.alloy.B.a.fits.delayed b).le) (hP.trans (by norm_num : (1/8:ℝ) ≤ 1))).trans_eq (Real.rpow_one (Φ b)))
end YM.QuadraticLocal.Advent.Sycamore
