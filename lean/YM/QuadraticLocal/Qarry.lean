import YM.QuadraticLocal.Close
/-!
# qlocal close interval restoring. Ticket, Marshal & Close path

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
-- eventually pay EVERY polynomial cost of restoring
set_option quotPrecheck false
local notation "Φd"=> Φ b
local notation "δ"=> forcedDivisor Z i
local notation "Op'"=> R.family.path.levels.clock.op i n -- weird
section wallets
-- Wall.Coupe. Local threshold.Pl.G. Pay powers using any stage raw Quote.Lessen factor outside, preserving exponential WP^1/2
include h g v l r
lemma bill_compact {u:ℕ}
    (hu:u+4≤ R.alloy.B.a.clock.J i)(hx:Φ b/2 ≤ Φ (i+1))(hγ : 2^(u+4) ≤ Φ b) {X' : ℝ}(hS:0≤X') (hβ:X'≤ Φ b) : X' * quoteR R (Ψ (i+1)).beta i ≤ min ((Φ b)^(-(u:ℝ))*δ) (Real.sqrt (quoteR R (Ψ (i+1)).beta i)):=by
    let f:=quoteR R (Ψ (i+1)).beta i; have hp:0< f:=Real.exp_pos _; have hphi:0< Φ b:= positive R b
    let z:=Φ b; have hz:=((S).fits.delayed b).le; have hW:= force_bill R h π Γ Ψ v l r hu; have ht := Real.rpow_le_rpow_of_nonpos (half_pos hphi) hx (show -(↑(u+4:ℕ):ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg _)); let ν:= Φ b; let hΩ := ((glyphBound (S) i).1); have hD : δ≤1:= (glyphBound (S) i).2; have h0:0<δ:= hΩ
    have hd : f* z^(u+3) ≤ δ:= by
       let A':=ν
       have hF := mul_le_mul_of_nonneg_right ht h0.le; have hQ := hW.trans hF; rw [Real.rpow_neg (half_pos hphi).le, Real.rpow_natCast,div_pow, ← one_div, div_div_eq_mul_div,one_mul] at hQ; -- rearr
       have hh : f ≤ (δ /(z ^ (u+3))) := by
          change (f) ≤ _; refine hQ.trans ?_; rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos hphi (u+4)) (pow_pos hphi (u+3)),pow_succ (Φ b) (u+3)]; change 2^(u+4)*δ*z^(u+3)≤ δ*(z^(u+3)*z); nlinarith only [mul_le_mul_of_nonneg_right hγ (show 0≤ δ*z^(u+3) from mul_nonneg h0.le (pow_nonneg hphi.le _))]
       exact (le_div_iff₀ (pow_pos hphi _)).mp hh
    apply le_min
    · rw [Real.rpow_neg hphi.le,Real.rpow_natCast, mul_comm _ (forcedDivisor ..),← div_eq_mul_inv]; refine (le_div_iff₀ (pow_pos hphi _)).2 (le_trans ?_ hd)
      have he : X'*(z^u) ≤ z^(u+3):= (mul_le_mul_of_nonneg_right hβ (pow_nonneg hphi.le u)).trans ((show (z*z^u) ≤ z^(u+3) from (by rw [← pow_succ']; exact pow_le_pow_right₀ hz (by omega)))) -- bracket error
      change X'*f*z^u≤ f*z^(u+3); linarith only [mul_le_mul_of_nonneg_left he hp.le]
    · have he : X'^2 * f ≤1:= calc
         X'^2*f ≤ z^2*f:= mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hS hβ _) hp.le
         _ ≤ f * z^(u+3):= by rw [mul_comm (z^2)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz (by omega)) hp.le
         _ ≤1 := hd.trans hD
      change X'*f ≤ _; apply Real.le_sqrt_of_sq_le; exact (show _≤ _ from by rw [mul_pow,pow_two f,← mul_assoc]; exact mul_le_of_le_one_left hp.le he)
end wallets
section restoring
set_option quotPrecheck false
local notation "Q*"=> Stoop.radius w (roof R (i+1) b)
local notation "fτ"=> Integration.LocalComparison.actualPush Z N n i
local notation "U'"=> Estate α (o i) P' J
local notation "V'"=> Estate α (o (i+1)) P J
local notation "Χ"=> min ((Φ b)^(-(s:ℝ))*δ) (Real.sqrt (quoteR R (Ψ (i+1)).beta i))
variable {Y₀:Estate α (o b) (Ψ b) J}
variable {T:∀ i,m≤ i→i≤ b→ Estate α (o i) (Ψ i) J}
include h g v l r hw hq
variable (hi:i<b)
variable (hT:Atlas (N:=N) R Ψ w o Y₀ m T)
local notation "x₁"=> T i l hi.le
local notation "x₂"=> T (i+1) (Nat.le_succ_of_le l) hi
include hT
lemma restores {ε:ℝ} (hs:s+4≤ R.alloy.B.a.clock.J i) (hz:Φ b/2≤Φ (i+1)) (hγ : 2^(s+4) ≤ Φ b) (hj: ∀ i,m≤ i→i≤b → roof R i b ^q ≤ min (Φ b) ((Φ b)^ε)): (T i l hi.le).canvas.Pays w (Ψ i).p.supportExponent ((Φ b)^ε) Χ := by
   have hg:= hT.covers i l hi.le; have hf:= hT.payment i l hi;
   refine ⟨Lamps.loan_monotone _ (Stoop.retake _ _ hq hw (roof_ge R i b) hg.budget) ?_,Hard.mono _ (Stoop.budget _ hq _ hw (roof_ge R (i+1) b) hf.1.wages) ?_⟩ -- binder order.T
   · rw [mul_one]; exact (le_min_iff.mp (hj i l hi.le)).2
   exact bill_compact R g h π Γ Ψ v l r hs hz hγ (pow_nonneg (zero_le_one.trans (roof_ge R _ b)) _) (le_min_iff.mp (hj (i+1) (Nat.le_succ_of_le l) hi)).1
omit hT h g v l r hw hq
variable (N b q m)
def Taken (ε:ℝ)(s:ℕ) (T:∀ i,m ≤ i→i≤ b → Estate α (o i) (Ψ i) J) :Prop:=∀ i:ℕ,∀ hl:m ≤ i,∀ hr:i < b,
    (T i hl hr.le).canvas.Pays w (Ψ i).p.supportExponent ((Φ b)^ε) (min ((Φ b)^(-(s:ℝ))*forcedDivisor Z i) (Real.sqrt (quoteR R (Ψ (i+1)).beta i)))
-- Atlas for some later Exterior, binding Step outputs. Commune.
include g h
variable (q:ℕ)
set_option quotPrecheck false
local notation "T'"=> ∀ i:ℕ,m≤ i→i≤ b→ E i -- λ notation
-- around single window ALL marks choices: length cert yields cost ≤ hats * sizes
lemma quarters (U:ℝ)(hx:0≤U) (k' r' s':ℕ) (ε:ℝ)(he:0<ε): ∀ᶠ b in atTop,∀ m ≤ b, Close R k' U m b→ ∀ k N π Γ n Ψ (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ), b≤ N→∀(α Θ':Type) [Nonempty α][DecidableEq Θ'][Fintype Θ'] (o:(i:ℕ)→Θ'→Site (R.family.side i n)) (J:Marker.Census Θ') (w:Θ'→ℝ)(Y₀:Estate α (o b) (Ψ b) J)(T:∀ i:ℕ,m≤ i→i ≤ b→Estate α (o i) (Ψ i) J), (∀ i,0<w i) → (∀ i:J.Mode,i.val.card≤r')→ Atlas (N:=N) R Ψ w o Y₀ m T→ Taken R m b Ψ w o ε s' T := by -- type param
   let g' := g
   filter_upwards [on_tail R g k' U (s'+4), covers_hat R g k' U,gives R g k' r' U hx ε he, gives R g k' r' U hx 1 zero_lt_one, (tendsto_const_nhds.add_atTop ((_root_.YM.Gauge.slopeConstant_pos g)|> fun h=> (S).S.divergent.const_mul_atTop h) : Tendsto (Φ) atTop atTop).eventually_ge_atTop (2^(s'+4))] with b hA hB hY hw' hs' m hm hC k N π Γ n Ψ v hb α Θ' a0 ihc fΘ o J w Y₀ T hw hq hT i hi hz
   exact restores R g h π Γ Ψ v hi w hw (lt_of_lt_of_le hz hb) o hq hz hT (le_trans (hA m hm hC) ((S).fits.mono hi)) (hB (i+1) m (Nat.le_succ_of_le hi) hz hC) hs' (fun i hi hz=> le_min (by have hP:=hw' m i hi hz hC; rw [Real.rpow_one] at hP; exact hP) (hY m i hi hz hC))
end restoring
end PaceR
end YM.QuadraticLocal.Advent
