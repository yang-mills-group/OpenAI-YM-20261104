import YM.QuadraticLocal.Pique
/-!
# Descending interval. Ticket, Marshal & Close path

Preserve exact marked histories on this *specific* Run for every finite cutoff and period.
Use native positions and aired representation. Roots parameters are fixed initially; while walking
one slot may always pay ANY support-exponent and keep its test arguments independent (no
merging different mark names to a convenient gas). Height weights remain P. Every time t with
P.mark demands sup. We discharge each successive Stage admission completely on the output.

This supplies repeated RAW growth and forced suppression (with division). The regular result
states growth, NOT homogeneous jet comparison yet. Needs to use `CarrierGuide.earns` directly
within each step for analytic packet comparison and allocate application. Client.P₁ accepts ANY
regular discrepancy on the same marked representation and independently any previous `w` FACTOR
as large as licenses (later stencils for ℂ/ℝ system witnessed).

Fixed k gates and weights per-coordinate. w may itself vary with i,cN,n etc (quantifier ideal
settled by caller) and may be LARGE e.g. 1/δ err charged per incoming mark. On log close intervals
whole product loses at most cumulative quote; bound after. This doesn't pay unlimited replicas
unless C.Frame over all mode sizes: constant for this k only. Describe stronger concerns in note.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
open Marker
variable {α I' Θ': Type}[DecidableEq Θ'] {J : Marker.Census Θ'}
variable (w:Θ'→ℝ) (hw:∀ i,0<w i) (r:i<N)
variable {j s:ℕ} (o:(j:ℕ)→Θ'→ Site (R.family.side j n))
variable (hr:∀ i,m≤ i→ i<b → o i=(R.family.path.levels.clock.op i n).ratio.parent ∘ o (i+1))
variable [Nonempty α][Fintype Θ'] {q:ℕ} (hℓ:q≤ R.alloy.B.a.clock.J m) (hq:∀ i:J.Mode,i.val.card≤q)
set_option quotPrecheck false
local notation "E"=> fun j => Estate α (o j) (Ψ j) J
local notation "hΞ"=> (Ψ i).p.supportExponent
local notation "f₁"=> R.family.path.levels.clock.op i n
local notation "X₁"=> budgetR R i
namespace PaceR
-- Paid wreath along Any.Epoch.W; restoration multiplicative on PRICE EACH mode.
def roof (R:Run G)(m b:ℕ):ℝ := ∏ i∈ Finset.Ico m b,budgetR R i
omit [Fintype Θ'] in
lemma roof_step (hx:i<b) : roof R i b = budgetR R i * roof R (i+1) b := by
   unfold roof; rw [← Finset.insert_Ico_add_one_left_eq_Ico hx, Finset.prod_insert (by simp)]
omit [Fintype Θ'] in
lemma roof_ge (R: Run G)(i b:ℕ): 1≤ roof R i b:= Finset.one_le_prod fun i h=> budget_pos R
include hw
local notation "toll"=> fun i=> Stoop.radius w (roof R i b)
lemma health (R:Run G) (b:ℕ)(i:ℕ) (v:Θ'): 0< Stoop.radius w (roof R i b) v:= div_pos (hw _) (zero_lt_one.trans_le (roof_ge R i b))
omit hw
lemma old (hx:i<b) : Stoop.radius w (roof R i b) = Stoop.radius (Stoop.radius w (roof R (i+1) b)) (budgetR R i):= by
   rw [roof_step R hx]; ext v; unfold Stoop.radius; rw [div_div,mul_comm (budgetR ..)]
structure Atlas (Ys: E b)(s:ℕ)(T:∀ i,s≤ i→i≤ b→ E i) : Prop where
   headS : s≤b
   topSame : T b headS le_rfl=Ys
   covers i (hi:s≤ i) (hx:i≤b) : (T i hi hx).canvas.Pays (toll i) (Ψ i).p.supportExponent 1 1
   payment i (hi:s≤ i) (hx:i<b) : pocket (N:=N) R Ψ (T i hi hx.le) (T (i+1) (Nat.le_succ_of_le hi) hx) (toll (i+1)) -- remove b'
include hw h K₀ v hℓ hq
variable (Y':Estate α (o b) (Ψ b) J)(he:b≤N)(hY:Y'.canvas.Pays w (Ψ b).p.supportExponent 1 1)
include he hY hr
local notation "sα"=> toll b

lemma claim (hmi:m≤ i)(hi:i≤b): ∃ T,Atlas (N:=N) R Ψ w o Y' i T:=by
   induction hi using Nat.decreasingInduction with
   | self=>
      let T (i:ℕ) (h:b≤ i)(hr:i≤b): E i:= (Nat.le_antisymm h hr) ▸ Y'; refine ⟨T,le_rfl,rfl,?_,fun i hi hj=> by omega⟩
      intro i h hF; have hi:= Nat.le_antisymm hF h; subst i
      have hx: T b h hF=Y':=rfl
      rw [hx,show toll b=w from funext (fun x=> by unfold roof Stoop.radius; simp)]
      exact hY
   | of_succ i hx ih=>
      obtain ⟨T,hT⟩:= ih (le_trans hmi (Nat.le_succ i))
      obtain ⟨Q',hQ⟩:= my_pocket R h D Q π Γ Ψ v K₀ hmi (toll (i+1)) (health w hw R b (i+1)) (by omega : i<N) (hr i hmi hx) (le_trans hℓ ((S).fits.mono hmi)) hq (T _ le_rfl hx) (hT.covers _ le_rfl hx)
      let T' (j:ℕ)(hx:i≤j)(he:j≤b) : E j := if hp:i<j then T j hp he else (le_antisymm hx (Nat.le_of_not_gt hp)) ▸ Q' -- motive annotation
      have hh : T' i le_rfl hx.le=Q':= dif_neg (by omega : ¬i < i)
      have hh' j (h:i<j)(hy:j≤b) : T' j h.le hy=T j h hy:= dif_pos h
      refine ⟨T',hx.le,(hh' b hx le_rfl).trans hT.topSame,fun j hj hz=>?_,fun j hj hz=>?_⟩
      · rcases eq_or_lt_of_le hj with hi|hi; · subst j; rw [hh]; dsimp only []; rw [old R w hx]; exact capacious R h π Γ Ψ v hmi _ (health w hw R b (i+1)) (lt_of_lt_of_le hx he) hQ
        rw [hh' j hi hz]; exact hT.covers _ hi hz
      rcases eq_or_lt_of_le hj with hi|hi; · subst j; rw [hh,hh' (i+1) (by omega) hz]; exact hQ
      rw [hh' j hi hz.le,hh' (j+1) (by omega) hz]; exact hT.payment j hi hz
-- consumer budgets full.PAY. plus orientation.
end PaceR
end YM.QuadraticLocal.Advent
