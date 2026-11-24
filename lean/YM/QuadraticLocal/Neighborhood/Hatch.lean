import YM.QuadraticLocal.HaloMix.Audiences
import YM.QuadraticLocal.Neighborhood.Era
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
variable {m n i b q k N:ℕ} (hwST:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
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
local notation "P↓"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
open Marker
namespace Sycamore
-- eventually pay EVERY polynomial cost of restoring
set_option quotPrecheck false
local notation "Φd"=> Φ b
local notation "Op'"=> R.family.path.levels.clock.op i n -- weird
namespace Moonlight
open Coat Travel PaceR VowsR Affinity MintClock Mentor Pavilion
variable {θ I₁:Type} [DecidableEq θ][Fintype θ] {J:Marker.Census θ}
variable {φ:ℕ→ℕ}(C:VowsR.LawScroll G φ)(Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
variable (Pt:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
variable (Uq:Pavilion.Purchased D R.rolls Q R.kit.target φ Q0 R.alloy.delay)
variable (hv:VowsR.Chamber C R.kit D Q Q0)
local notation "salary"=> Q0.salary Y I Pt
local notation "μΖ"=> salary.price
local notation "ωΖ"=> salary.enroll
local notation "κP"=> Pavilion.Degree D R.rolls Q (R.kit).target φ Q0 (A).delay Pt Uq
local notation "tΩ"=> Delay.fineMonitor G L
local notation "Ω"=> (Delay.fineMonitor G L xd)^κP
namespace Orbit
-- aids.Public.Material persistence, Growth coupon buys before any period/time/call

variable (D0: Curriculum R)
/-! # Initialize with just ROOTED costs, on same speeches (one actual unmarked campaign).
 `Rough antenna` expansion: `ForecastK` spent only on Mark part proportional to given
 theta. Job all levels.W. Input permit.Perhaps Birth at b.W`, no K weights beyond Raw
 vacuum allowance: actual computed from path data, not assuming it at these levels.
 Output per-marker invoicing.May carry into Capsule with stronger support convention first.
-/
open QuadraticLocal.Neighborhood QuadraticLocal.Neighborhood.Aperture
open Extra.Multi Quantity
variable (Hp:Quantity.Park R.rolls R.alloy.delay)
local notation "UΩ"=> (Pavilion.Quantity.book R.rolls R.alloy.delay Hp (step_paid S i))
local notation "Yζ"=> (Delay.fineMonitor G L xd)^UΩ
local notation "K"=> R.alloy.B.a.clock.forcedAllowance
local notation "δ" i:max=> (Ψ i).p
local notation "E₀" j:max=> (R.alloy.B.a.budget j)
local notation "Bew" p:max u:max=> Quantity.arena (BudgetPoint.power p) ( BudgetPoint.order p ) ( BudgetPoint.B p ) u
include hv Hp
lemma prepaid (s:ℕ)(he:s≤Y) : Quantity.arena (E₀ (i+1)).power (E₀ (i+1)).order (E₀ (i+1)).B s ≤ (Yζ) ∧ Yζ ≤ (budgetR R i):= by
    let hT:=Quantity.fitted R.rolls R.alloy.delay Hp (step_paid S i) xd (R.alloy.B.valid.pays i); obtain ⟨hM,hF,hZ,hG,hU,hQt,hV1,hL⟩:= zones D Q A F hv.station.pledge (m:=i);
    constructor
    · apply le_trans (Pavilion.Quantity.park_mono _ _ _ he); rw [hZ.2.1,hZ.1,hQt]; exact hT.pre
    unfold budgetR; rw [PriceCompiler.beta_eq R.alloy.B.valid i]; exact hT.roof
-- actual post-height geometry costs at all b, horizon.Power.Sub.Asset.Shape. footprint always active.
lemma postpaid (s:ℕ)(he:s≤ I): Bew (X) s ≤ ( Yζ ) ∧ Yζ ≤ (budgetR R i)∧ Yζ ≤ (Φ i)^(1/3:ℝ) ∧ 4 ≤ Φ i:= by
    let hT:=Quantity.fitted R.rolls R.alloy.delay Hp (step_paid S i) xd (R.alloy.B.valid.pays i); obtain ⟨hM,hF,hZ,hG,hU,hQt,hV1,hL⟩:= zones D Q A F hv.station.pledge (m:=i);
    refine ⟨?_, (prepaid R D Q C Q0 hv Hp 0 (Nat.zero_le _)).2, hT.both.trans (min_le_right ..), hT.lease.1⟩; apply le_trans (Pavilion.Quantity.park_mono _ _ _ he); rw [hF.2.1,hF.1,hM]; exact hT.post
omit hv Hp
include v l
lemma rooms (r:i≤N): K i ≤1/2∧ Hard.Rent (Ψ i).activities.forced (Ψ i).activities.K (Ψ i).p (Ψ i).p.supportExponent (K i):= by
    let h':=(later R π Γ Ψ v l r).truep.valid.labels; constructor
    · unfold Calendar.forcedAllowance Calendar.monitor; let v:= Real.log (Real.log (Φ i)); have hv:1 ≤ Real.exp (v^2):= Real.one_le_exp (sq_nonneg _); have hh:= Real.one_le_rpow hv (by norm_num: (0:ℝ) ≤ 1/5); apply le_trans (Real.exp_monotone (neg_le_neg hh)); rw [Real.exp_neg]; apply le_trans (inv_anti₀ zero_lt_two ((by linarith only [Real.add_one_le_exp 1] : (2:ℝ) ≤ Real.exp 1))); rw [← one_div]
    exact Hard.rentValid h'.forced h'.boundK
omit v l
variable {k₁ :ℕ}
def amplification (R: Run G)(b k₀:ℕ) := Bew (R.alloy.B.a.budget b) k₀
private lemma monoM (p:BudgetPoint)(k:ℕ): 0≤ muQ p k ∧ muQ p k ≤ Bew p k ∧ muE p k ≤ Bew p k:=by
    have hu:0≤ muQ p k:= by unfold muQ Extra.Multi.siteFactor; positivity
    have ht:0≤ muE p k:= mul_nonneg (mul_nonneg (scarf_pos p).le (Nat.cast_nonneg _)) hu
    exact ⟨hu,(le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right ht),le_add_of_nonneg_left (show 0≤1+muQ p k from by linarith)⟩
local notation "u" i:max=> amplification R i k₁
include hv Hp
lemma pledge {ε:ℝ}(hz:0≤ε)(hq:k₁≤ (I))(he:ε≤(Φ i)⁻¹): 0≤ (amplification R i k₁)*ε ∧ (amplification R i k₁)*ε ≤ Pavilion.closedRoom (Φ i) ∧ Pavilion.closedRoom (Φ i) ≤1/2:= by
    obtain ⟨ht,hZ,hP,hB⟩:= postpaid R D Q C Q0 hv Hp _ hq; let y:=Φ i; 
    have hx:= positive R i; have h:1≤y:= ((S).fits.delayed i).le
    constructor
    · exact mul_nonneg ((monoM X k₁).1.trans ((monoM X k₁).2.1)) hz
    refine ⟨ le_trans (mul_le_mul (ht.trans hP) he hz (Real.rpow_nonneg hx.le _)) ?_,?_⟩
    · change y^_ * y⁻¹ ≤ y^(_ :ℝ); rw [← Real.rpow_neg_one, ← Real.rpow_add hx]; norm_num; exact le_rfl
    apply le_trans (Real.rpow_le_rpow_of_exponent_le h (by norm_num: -( (2:ℝ)/3 ) ≤ -(1/2:ℝ)))
    rw [Real.rpow_neg hx.le,← Real.sqrt_eq_rpow]; apply le_trans (inv_anti₀ zero_lt_two (show (2:ℝ) ≤ Real.sqrt y from Real.le_sqrt_of_sq_le (by linarith))); rw [← one_div]
-- tie ι initializing from actual sensors when buying at b
variable {V:Type*} [DecidableEq V]
variable {Xℓ:θ→Type} [∀ i,AddCommGroup (Xℓ i)][∀ i,Module ℝ (Xℓ i)]
variable (Actors:∀ i,Set (Xℓ i))(uK:∀ i, Submodule ℝ (Xℓ i))
variable (o:(j:ℕ)→θ→Site (R.family.side j n))(Loc:(j:ℕ)→θ→Support (R.family.side j n))
local notation "U'" i:max=> Kin R Ψ Actors uK o Loc i
local notation "T" i:max=> Estate (Affinity.Wallet Actors) (o i) (Ψ i) J
local notation "L0" i:max=> Affinity.Collared ( Loc i ) Actors uK
variable {ε:ℝ}
variable (w:θ→ℝ) (hw:∀ i,0<w i)
local notation "S₁" i:max=> (Ψ i).p.supportExponent
-- reserve two and one (correspondingly) input when stated as in absolute Θ.
variable (hf: Extra.Multi.Occupancy (o i) k₁)
variable (K₀:Estate (Affinity.Wallet Actors) (o i) (Ψ i) J)
include hv Hp v l hf hw
lemma invite (r:i≤N)(hx:k₁ ≤ R.alloy.B.a.clock.J i)(h:0≤ε)(he:ε ≤ ( Φ i )⁻¹)(hP: (L0 i) (Ψ i) K₀.canvas)(hH:RootsE K₀.canvas.E w ((Ψ i).p.supportExponent+2) ε)(hF: RootsK K₀.canvas.K w ((Ψ i).p.supportExponent+1) ε): Kin R Ψ Actors uK o Loc i K₀ w (amplification R i k₁*ε):=by
   let a:=(Ψ i).p; let v':=(later R π Γ Ψ v l r).truep.point; obtain ⟨hz,hK⟩:= rooms R π Γ Ψ v l r; obtain ⟨hq,hZ,hr⟩:= monoM X k₁; have ht := ( RootsE.meter hw K₀.canvas.E hf hH h ); have hp:= (RootsK.assemble hw K₀.canvas.K hf hF h hK)
   have hE₀: amplification R i k₁ * ε ≤1/2:= (pledge R D Q C Q0 hv Hp h hx he|>.2.1).trans ((pledge R D Q C Q0 hv Hp h hx he).2.2)
   have hK' : muQ a k₁ * ε ≤ amplification R i k₁ * ε:= mul_le_mul_of_nonneg_right (by unfold a; rw [v']; exact hZ) h -- v'.symm ▸ rewr possible changes both?
   refine ⟨hP,Lamps.loan_monotone _ ht ?_, Throng.Hard.Pair.mono _ hp ?_ hK'⟩
   · exact mul_le_mul_of_nonneg_right (by change muE a k₁≤ _; unfold a; rw [v']; exact hr) h
   change K i+ muQ a k₁*ε ≤1; linarith only [hz,hK',hE₀]
-- report roots from this work. useful even for other marks still performing.Lo.Est.P_Currency.Fr.Actor.Geo.Health``.
omit Hp hf
variable (Vb:Estate (Affinity.Wallet Actors) (o b) (Ψ b) J) (T':∀ i:ℕ,m≤ i→i≤b → (Estate (Affinity.Wallet Actors) (o i) (Ψ i) J))
variable (h:Chorus (N:=N) R D Q Ψ Q0 Uq D0 w Actors uK o Loc ε q m b Vb T')
local notation "w_B" j:max=> Stoop.radius w (extent R D Q Q0 Uq D0 j b)
local notation "Gk"=> forcedDivisor Z i
include h
lemma audiences (r:i < b)(he:b ≤ N)(Sx:Set θ)(hη:ε≤1): let V0:=( Orbit.strip R Ψ Actors o (T' i l r.le) Sx )
    let δi:ℝ:= (Moonlight.volume R D Q Q0 (D0 i) Uq)
    let P':= V0.canvas
    RootsE P'.E (w_B (i+1)) ( (Ψ i).p.supportExponent+1+1 ) (3*(δi*ε))∧ RootsK P'.K (w_B (i+1)) ((Ψ i).p.supportExponent) (((γ)^(-(q:ℝ))*forcedDivisor Z i)*ε) ∧ Throng.Hard.Pair P'.K (w_B (i+1)) (Ψ i).p.B (Ψ i).p.supportExponent ( R.alloy.B.a.clock.forcedAllowance i ) (((γ)^(-(q:ℝ))*forcedDivisor Z i)*ε):=by
    intro V0 δi P'; let W':= strip_hall R D Q π Γ Ψ v C Q0 Uq hv D0 w hw Actors uK o Loc Sx he hη h; have hW:= W'.orders i l r; let v':=(T' i l r.le).canvas; have hr:∀ v,0<(w_B (i+1)) v:= health R D Q Q0 Uq D0 w hw _ b; let Ht:= hW.lateLedger
    let w_:= K i; have hb: wp ≤ w_^2:= Consequence.calmPrice R.kit ( ?_ : (Ψ (i+1)).beta∈ Shoot.band S (i+1) ); swap; · let hs:= (later R π Γ Ψ v (Nat.le_succ_of_le l) (le_trans r he)); rw [hs.beta]; exact (R.T.sticks N n|>.prices _ (Nat.zero_le _) (le_trans r he)).2
    have hz: 0≤w_:= Real.exp_nonneg _; have hh:=le_trans ((rooms R π Γ Ψ v l (r.le.trans he)).1) (by norm_num : 1/2 ≤(1:ℝ)); have hb:=hb.trans (show _≤ w_ from by change w_^2≤w_; nlinarith only [hz, (show w_ ≤ 1 from hh)] )
    exact ⟨RootsE.output hr P'.E hW.billE, RootsK.output hr P'.K Ht,Throng.Hard.Pair.mono _ Ht hb le_rfl⟩
end Orbit
end Moonlight
end Sycamore
end YM.QuadraticLocal.Advent
