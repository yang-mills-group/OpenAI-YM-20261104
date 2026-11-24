import YM.IterationFour.Vacuum.Step

/-!
# The exact unmarked recurrence

A (sufficient) board of *scalar* price inequalities. Keep every multiplier
on the inherited error per step, not just convergence at a literal i. Distinct
currencies for the rho/flat beta costs and E and K. Norm/analytic supplies
from RG01/03 are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Vacuum
open Lattice Wilson RG Function MeasureTheory Filter Currency Render
open AnalyticBridge VerifiedReset
open scoped Topology BigOperators ContDiff
variable {G : Gauge}

/-- Finite Fk truncation **inputs** at levels m≤N. Additional packets only,
    keep all the Wilson base, kinetic, noise, prescriptions already at the
    actual path. This is a consumer: neither choosing coefficients nor claiming
    connection to Fk diagrams.

    At `m<N`, in beta units the printed order R includes powers 0,...,R-2.
    `predict` evaluates it in the actual fine coupling. In `alpha`, specify
    how to consume the deterministic update (see `Early`). -/
structure Plan (C : Family G) (N q r : ℕ) where
    layers i : List (Piece G (C.side i q))
    orders : ∀ i, i≤N → gradings (layers i) r
    coefficient : ℕ→ℕ→ℝ
    alpha : ℕ→ℝ

namespace Plan
variable {C : Family G} {N q r : ℕ} (P : Plan C N q r)
def poly (i : ℕ) (g : ℝ) := ∑ e∈Finset.range (r-2+1), P.coefficient i e * g^e
def predict (i : ℕ) := if i=N then C.path.β N q i else C.path.β N q (i+1)+P.poly i (g C N q (i+1))
end Plan

/-- Prices per step, issued on a fixed order/horizon, real/norm positive
    majorants; no stipulated formula for sizes of the local-input estimates.
    Eta version in `Admitted`. `response` is for pricing the e-natural from
    the previous reclosure (`read_exponent`). `taylor` pays RG01 local Taylor
    production (incl cumulant/analytic costs at the full local class);
    `transport` all RG03 pre-reset operations not charged elsewhere (those
    on the inherited error debited in `repeatCost`); `outside` any other
    additions needed for exceptional regions/seeds here. -/
structure Pocket where
    repeatCost : ℝ
    taylor : ℝ
    transport : ℝ
    response : ℝ
    outside : ℝ
    forceEarly : ℝ
    forceGoal : ℝ
    prices_pos : 0≤repeatCost ∧ 0≤taylor ∧ 0≤transport ∧ 0≤response ∧ 0≤outside
namespace Pocket
variable (v : Pocket)
def single := v.taylor+v.transport+v.outside
def due (known drift : ℝ) := v.repeatCost * known + v.single + v.response * drift
lemma single_nn : 0 ≤ v.single := by rcases v.prices_pos with ⟨_,h,h',_,hw⟩; unfold single; positivity
lemma due_nn {k d : ℝ} (hk : 0 ≤ k) (hd : 0 ≤ d) : 0 ≤ v.due k d := by
    have h := v.single_nn; obtain ⟨hp,_,_,hl,_⟩:=v.prices_pos; unfold due; positivity
end Pocket

/-- Induction at exponent s,sigma and uniform K. Wave precision requested `w≥s`,
    not re-spent at each iteration. Use smaller exponents in projections to real
    output. -/
structure Purse where
    sigma : ℝ
    w : ℝ
    ahead : sigma≤w
    fare : ℝ
    theta : ℝ
    pos : 0<theta
    fits : theta<1
    cash : 0<fare
    above : 0 ≤ sigma
namespace Purse
variable (Y : Purse)
def limit (a : Levels G) (m : ℕ) := Y.fare * weight a Y.sigma m
def guardBill (a : Levels G) (m : ℕ) := weight a Y.w m
lemma spends {a : Levels G} (h : G.Simple) : Antitone (Y.limit a) :=
    fun _ _ he=> mul_le_mul_of_nonneg_left (across a h Y.above he) Y.cash.le
lemma limit_pos (a : Levels G) (m : ℕ) : 0 < Y.limit a m := mul_pos Y.cash (weight_pos ..)
lemma guard_pos (a : Levels G) (m : ℕ) : 0 < Y.guardBill a m := weight_pos ..
end Purse
variable {N q r : ℕ}

/-- Overall amplification multiplier on early regular error (includes the
    subsequent coupling adjustment term). Also keep a unit cap on H itself
    for the beta estimate. -/
def wall (a : Levels G) (m : ℕ) {n : Side} (S : List (Piece G n)) :=
    adjusting a m+ shiftBill S (B a m)*((a.budget m).threshold^2)⁻¹

variable {C : Family G}

lemma wall_nn (a : Levels G) {n : Side} (m : ℕ) (S : List (Piece G n)) {p : BudgetPoint} (he : permits S p) :
    0 ≤ wall a m S := add_nonneg (Time.base_nonneg G (a.params m)).1
      (mul_nonneg (shift_nn S he (WardBin.hot a m)) (inv_nonneg.mpr (sq_nonneg _)))
lemma paying_owed (a : Levels G) {n : Side} (m : ℕ) (S : List (Piece G n)) (l H : ℝ) :
    owed a m S l H=wall a m S*H+shiftBill S (B a m)*l := by
  unfold owed wall conversion; ring

namespace Reset
lemma brake (a : Levels G) (m : ℕ) {α H L : ℝ} (h : H ≤ L) : let p:= a.budget m; let q:= a.params m; Collection.softNeed G p q.clip q.width q.paths α H ≤ Collection.softNeed G p q.clip q.width q.paths α L := by
  let p := a.budget m; let P:=a.params m
  dsimp only []
  have hy := AnalyticBridge.VerifiedReset.Collection.budget_pos p G P.clip P.width_pos P.paths_pos.le
  have hE : Quotes.softReset G p H ≤ Quotes.softReset G p L:= by
    have hR := AnalyticBridge.VerifiedReset.Residual.loss_pos G p
    have hq : 0 ≤ (1-Real.exp (-(1:ℝ)))⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))
    unfold Quotes.softReset Push.AbsoluteSums.Footprint.payment Push.AbsoluteSums.Footprint.degreeIncome
    gcongr
  refine add_le_add hE (mul_le_mul_of_nonneg_right ?_ hy.2.2)
  have hh:= (a.budget m).threshold_pos; have ht:= pair_nonneg G (a.budget m); unfold Collection.hitNeed; gcongr
lemma cheaper (a : Levels G) (m : ℕ) {α H L w γ : ℝ} (h : H ≤ L)
    (hp : Duty a m α L w γ) : Duty a m α H w γ := by
   obtain ⟨k,u,hx,hv⟩:=hp; exact ⟨k,u,(brake a m h).trans hx,hv⟩
end Reset

/-- Sufficient bills imposed on one step AFTER its true L,S adjacency and
    horizon/order have been fixed. E.g. Taylor powers in `single` **at the
    fine level**, then pay alignment with the displayed `wall`. These are not
    consequences of monotonicity of weights alone. -/
structure Room (C : Family G) (Y : Purse) (P : Plan C N q r) (m : ℕ) (t : Pocket) : Prop where
    decent : WilsonStartup.Decent (C.path.levels.params m).clip (C.path.levels.budget m)
    width : Geo.Width (C.path.levels.budget m) (C.path.levels.params m).clip (C.path.levels.params m).width
    format : permits (P.layers m) (C.path.levels.budget m)
    predicted : P.predict m∈stripe (B C.path.levels m)
    supplies : Y.limit C.path.levels m + unitBill (P.layers m) (B C.path.levels m) ≤
      C.path.levels.clock.allowance m
    hard : Duty C.path.levels m (P.alpha m) (t.due (Y.limit C.path.levels (m+1)) (Y.guardBill C.path.levels (m+1)))
      t.forceEarly t.forceGoal
    hard_paid : t.forceGoal ≤ C.path.levels.clock.forcedAllowance m
    extracted : (1+wall C.path.levels m (P.layers m))*t.repeatCost ≤ Y.theta
    pays : (1+wall C.path.levels m (P.layers m))*(t.single+t.response*Y.guardBill C.path.levels (m+1))+
      shiftBill (P.layers m) (B C.path.levels m)*Y.guardBill C.path.levels m ≤
      (1-Y.theta)*Y.limit C.path.levels m

variable (P : Plan C N q r) (Y : Purse) {m : ℕ} {t : Pocket}
lemma limits (hg : G.Simple) (he : Room C Y P m t) (x : ℝ) (hx : 0≤x) (hp : x≤Y.limit C.path.levels (m+1)) :
    let y:=t.due x (Y.guardBill C.path.levels (m+1)); let l:=Y.guardBill C.path.levels m; let a:= C.path.levels
    y≤ Y.limit a m ∧
      owed a m (P.layers m) l y ≤ Y.theta*x+(1-Y.theta)*Y.limit a m ∧
      owed a m (P.layers m) l y ≤ Y.limit a m ∧ 0≤ owed a m (P.layers m) l y ∧
      conversion a m l y ≤ (Y.fare+1)*weight a (Y.sigma-2) m := by
  intro y l a; let S:=P.layers m
  have hz := he.pays
  have hy := t.due_nn hx (le_of_lt (Y.guard_pos a (m+1)))
  change 0≤y at hy
  have ht := wall_nn a m S he.format
  have hl := mul_nonneg (shift_nn S he.format (WardBin.hot a m)) (le_of_lt (Y.guard_pos a m))
  have h₁ : owed a m S l y+y ≤ Y.theta*x+(1-Y.theta)*Y.limit a m := by
    calc
      _ = ((1+wall a m S)*t.repeatCost)*x + ((1+wall a m S)*(t.single+t.response*Y.guardBill a (m+1)) +
            shiftBill S (B a m)*Y.guardBill a m) := by rw [paying_owed]; unfold l y Pocket.due a; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right he.extracted hx) he.pays
  have h₂ : x≤Y.limit a m:= hp.trans (Y.spends hg (Nat.le_succ _))
  have h₃:0≤ owed a m S l y:= (paying_owed ..) ▸ add_nonneg (mul_nonneg ht hy) hl
  have h₄: Y.theta*x+(1-Y.theta)*Y.limit a m ≤ Y.limit a m:= by
    have hx:=mul_le_mul_of_nonneg_left h₂ Y.pos.le; linarith
  have H : y ≤ Y.limit a m:= (le_add_of_nonneg_left h₃).trans (h₁.trans h₄)
  have h₅:= le_trans (le_add_of_nonneg_right hy) h₁
  refine ⟨H,h₅,h₅.trans h₄,h₃,?_⟩
  unfold conversion
  have hx : y / (a.budget m).threshold^2 ≤ Y.fare * weight a (Y.sigma-2) m := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (Y.fare * weight a Y.sigma m)*B a m := by
        exact mul_le_mul H (threshold_receipt ..) (inv_nonneg.mpr (sq_nonneg _)) (le_of_lt (Y.limit_pos a m))
      _ = _ := by rw [mul_assoc,mul_comm (Currency.weight ..), beta_payment]
  calc
    _ ≤ _ := add_le_add hx (weight_le a m (show Y.sigma-2≤Y.w by linarith only [Y.ahead]))
    _ = _ := by ring
end YM.IterationFour.Vacuum
