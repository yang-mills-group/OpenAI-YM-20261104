import YM.QuadraticLocal.Neighborhood.Initialize
import YM.QuadraticLocal.Neighborhood.ModeEstimate
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

open QuadraticLocal.Neighborhood QuadraticLocal.Neighborhood.Aperture QuadraticLocal.Neighborhood.Origin
open Extra.Multi Quantity
/-!
# Large-load warm startup

 Starting at any b, including actual Wilson top. Buy at standard stage powers
 (upper locality and test powers at that p, halo geometry may include any
 stipulated Region+Orientation.H from caller). **No seed/positivity hypotheses**
 for ANY mark test. Uses canonical construction paying its actual startup `_top`
 unmarked K budget and smooth E at every i. Then for a family of local cutoffs
 or supplied INSERTION `Lamps` given (i.e., actual complete regular model
 exponent factors and a joint protocol of all marks wanted, with these tests),
 if those cylinders have the indicated regular input bound on good fields &
 full-group bound (any signed presentation), bought at announced radius,
 build actual `V.Env`, automatically adding every forced complement & mask
 with the header and epoch.A.Book.C._Sensor.Walk`.

  - permits startup even for multiset combinations in log not only linear singletons.
       Rank mask: each input represents an explicitly tagged unmasked exponent term (gauge,
       UsesCurrent on given complete footprint, not assumed analytic), and can be designated
       GLOBAL.
  - size assumptions meant to include `I_s` units and stencil test scans. If radial
       fiber counts >1 accumulate first. We do not do any preimage renaming or rescaling
       of these Mark inputs. publish with exact L_D costs separately afterwards.
  - output same polynomial up to the formal sum. Every forced entry carries actual flag
       of H.Y. `Expect.World.Owner.Region.Health.Measure.Price`
  - strong force reserve (at b inclusive already even <β^{-d}*sqrt(ŵ) for all published
       d ≤ J_b-1). may only bound *marked* part's proportional amplitude dC (since actual
       vacuum kept at constructor's caps). Mark input ε positive, otherwise choose some
       positive budget for it. the reported proxy ε in `Energy` Θ covers both normalized
       cylinders' amplitude and Hold.Shape requests.W.Unit.Phase.Price.Engine. It's not a split
       learned only after choosing one tuple of tests. Reader repeats at ANY radius used
       with these hypotheses *already satisfied*, including ε-floor for a collection of
       replicated globally integrable cylinders*; choose a smaller radius at provisioning to put
       them there (e.g. power in `θ` if using `Formula.*` comparison; price capacity
       throughout is relative to THAT declared inquiry, not some higher linked therapy budget).
       Not deriving analytic coefficient correspondence or history bound for mass of specific
       graph columns from this statement: supplies operation/context-free bootstrap on any
       given such input kernels as used in represented-lemma.
-/
variable (HP:Pavilion.Quantity.Park (R.rolls) (R.alloy.delay))
local notation "bW" j:max=> R.alloy.B.a.budget j
local notation "Y℃"=> R.alloy.B.a.clock.J i
local notation "Sup"=> (Ψ i).p
local notation "φi"=> (X)
local notation "δB"=> forcedDivisor Z i
-- binding is ALWAYS at that carrier; tie cost.Power.Peps.Property.Invoice.Observer`
private lemma coversQ (p:BudgetPoint) (k:ℕ) : 1 ≤ arena p.power p.order p.B k ∧ muQ p k ≤ arena p.power p.order p.B k ∧ muE p k ≤ arena p.power p.order p.B k:=by
    have hu:0 ≤ muQ p k:= by unfold muQ Extra.Multi.siteFactor; positivity
    have ht:0 ≤ muE p k:= mul_nonneg (mul_nonneg (scarf_pos p).le (Nat.cast_nonneg _)) hu
    exact ⟨ ( show 1≤1+muQ p k + muE p k from (le_add_of_nonneg_right hu).trans (le_add_of_nonneg_right ht) ),( le_add_of_nonneg_left zero_le_one ).trans (le_add_of_nonneg_right ht), le_add_of_nonneg_left (by linarith only [ht,hu] : 0 ≤ 1+muQ p k)⟩
private lemma speed (B:ℕ): (Willow.haloSlack B)⁻¹ ≤ Extra.Multi.siteFactor B:=by
    unfold Willow.haloSlack Willow.area siteFactor; push_cast; rw [one_div,inv_inv]; let d:ℝ:= ↑B; have he : 0≤d:= Nat.cast_nonneg _; let t:ℝ:= 2*(16*d+9); have hP: 2*(d+d+1) ≤ t:=by unfold t; linarith only [he];
    calc
       _ = (2*(d+d+1))^4 := by unfold d; ring
       _ ≤ t^4 := pow_le_pow_left₀ (by linarith) hP _
       _ ≤ _ := le_mul_of_one_le_left (by unfold t; positivity) (Real.one_le_exp zero_le_one)

include hv HP
lemma rate (μ:ℕ)(hi: μ ≤ Y℃) : Aperture.muQ (R.alloy.B.a.budget i) μ * (Φ i)⁻¹ ≤ Willow.haloSlack ( ( R.alloy.B.a.budget i ).B ) := by
   let S':=(φi); let E:= S'.B
   let k:= Willow.haloSlack E; let y:= Φ i; have hy:= positive R i; have h:1≤y:= (R.alloy.B.a.fits.delayed i).le; have hk: Quantity.arena ( S' ).power S'.order E 1 ≤ y^(1/3:ℝ):= by
       let H0:1 ≤ (Y℃):= by have hw:= (S).clock.adm i; omega
       exact (postpaid R D Q C Q0 hv HP 1 H0).1.trans ((postpaid R D Q C Q0 hv HP 1 H0).2.2.1)
   let hb':= speed E; have hp:k⁻¹ ≤ y^(1/3:ℝ):= hb'.trans (by simpa only [Aperture.muQ,Nat.cast_one,one_mul] using (((coversQ (φi) 1).2.1).trans hk)) -- prove siteFact eq
   have he:= Willow.spare_pos E; have hG := postpaid R D Q C Q0 hv HP μ hi
   refine le_trans (mul_le_mul_of_nonneg_right (((coversQ (φi) μ).2.1).trans (hG.1.trans hG.2.2.1)) (inv_nonneg.mpr hy.le)) ?_
   change y ^(_ :ℝ) * y⁻¹ ≤ k; unfold y; rw [← Real.rpow_neg_one, ← Real.rpow_add hy]; refine le_trans (Real.rpow_le_rpow_of_exponent_le h (?_ : _ ≤ -(1/3:ℝ))) ?_; · norm_num
   rw [Real.rpow_neg hy.le]; exact (inv_anti₀ (inv_pos.mpr he) hp).trans_eq (inv_inv _)
section Public
variable {Xℓ:θ→Type} [∀ i,AddCommGroup (Xℓ i)][∀ i,Module ℝ (Xℓ i)]
variable (Actors:∀ i,Set (Xℓ i))(uK:∀ i, Submodule ℝ (Xℓ i))
variable (w:θ→ℝ) (hw:∀ i,0<w i) (ε:ℝ)
variable (o:(i:ℕ)→ θ→ Site (R.family.side i n))(Loc:(i:ℕ)→ θ→ Support (R.family.side i n))
variable {ℒ:Type}[Countable ℒ]
variable (D': Lamps (Affinity.Wallet Actors) ℒ G (Ψ i).p (o i) J)
local notation "T"=> Estate (Affinity.Wallet Actors) (o i) (Ψ i) J
local notation "Θ"=> QuadraticLocal.Neighborhood.Origin.shifts D'
local notation "θ₁"=> (Ψ i).p.supportExponent
variable {μ:ℕ}
variable (hE: Neighborhood.Aperture.RootsE D' w ( (Ψ i).p.supportExponent+2) ε)
    (he:0<ε)(hz:ε ≤ (R.alloy.B.a.clock.hatBeta i)⁻¹)(hH: Extra.Multi.Occupancy (o i) μ)(hU:μ ≤ R.alloy.B.a.clock.J i)
local notation "p₁"=> Willow.haloSlack (Ψ i).p.B
variable (hX:Affinity.Taut (Loc i) Actors uK D')(hG: QuadraticLocal.Neighborhood.Origin.Global D' w ( (Ψ i).p.supportExponent+2) ε)
include v l
variable (h:i≤N)
include h he hz hG hw hH hU μ
local notation "cL"=> muQ (Ψ i).p μ
local notation "κ"=> (Φ i)⁻¹/ε
lemma ropes : (Θ).Budget w (Ψ i).p.B ( (Ψ i).p.supportExponent+1) p₁ ∧ 1≤ κ ∧ ( Throng.Hard.shift Θ κ ).Budget w (Ψ i).p.B ( (Ψ i).p.supportExponent+1) p₁:= by
   let L_ := (Ψ i).p; let y:= Φ i; have h0: μ ≤ Y℃:= hU; have hg := ( later R π Γ Ψ v l h ).truep.point; let t' := κ;
   have he': 1 ≤ κ:= (one_le_div he).mpr hz
   have ht: ( κ )*((cL)*ε) ≤ p₁ := by
      rw [ hg,(show _/ε*( _ *ε)= Aperture.muQ ( R.alloy.B.a.budget i ) μ* (Φ i)⁻¹ from (by field_simp)) ]; exact rate R D Q C Q0 hv HP μ h0
   have hx:0≤ cL:= by unfold muQ Extra.Multi.siteFactor; positivity
   have hs:= Origin.subscriber hw D' hG hH he.le
   obtain ⟨f,hf,hL⟩:= hs.earned; refine ⟨⟨_,hf,fun i=>budget_loosen (hL i) ((le_mul_of_one_le_left (mul_nonneg hx he.le) he').trans ht) ⟩, he', ?_⟩;
   obtain ⟨f,hf,hF⟩:= (Origin.scaler («P»:=Ψ i) hw (Θ) hs (zero_le_one.trans he')).earned; exact ⟨_,hf,fun i=>budget_loosen (hF i) ht⟩

local notation "α"=> amplification R i μ*ε
local notation "Bq"=> forcedDivisor R.family i
local notation "fp"=> forcedDivisor (R.family) i* (Φ i )^(-(q:ℝ))
variable (hPa:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
include hPa hE hX
variable (hW:q+1 ≤ R.alloy.B.a.clock.J i)
-- keeps implemented K.At constructed campaign.Auth payload
include hW
lemma theatre : ∃ (K: QuadraticLocal.Hard (Affinity.Wallet Actors) (Ψ i).p (Ψ i).activities.forced (Ψ i).activities.K (o i) J), let kR : Estate _ (o i) (Ψ i) J:= {locale:=ℒ,seats:=inferInstance,canvas:=⟨D',K⟩}; Kin R Ψ Actors uK o Loc i kR w (amplification R i μ*ε) ∧ Throng.Hard.Pair K w (Ψ i).p.B (Ψ i).p.supportExponent (forcedDivisor R.family i* (Φ i )^(-(q:ℝ))) (( forcedDivisor R.family i* (Φ i )^(-(q:ℝ)))*ε) ∧ ∀ a U, Summable (fun j=>QuadraticLocal.Neighborhood.Origin.whole D' a j U) ∧ kR.canvas.density a U= (↑((Ψ i).eval U):ℂ) • ( Poly.pass (∑' j, QuadraticLocal.Neighborhood.Origin.whole D' a j U )):= by
   have hp:=(later R π Γ Ψ v l h).truep.point;
   obtain ⟨h',hK',hG'⟩:= ropes R D Q π Γ Ψ v l C Q0 hv HP Actors w hw ε o D' he hz hH hU hG h -- guess order Loc redundant
   obtain ⟨f,hf,hT⟩:= Uplink.runway R (hv.ready C) D Q π Γ Ψ v hv.station l hPa hW h
   obtain ⟨U,B,⟨u⟩,hb⟩:= hT.room
   let M:= Origin.set D' u hb
   have hx:= RootsE.meter hw D' hH hE he.le; let p:= (Ψ i).p; have hvX:= Origin.echoes hw D' u hb hK' hG'; have hQ:= Origin.unchanged u hb hX; let y:= (Φ i); let ψ:= Bq; have hy:= positive R i; have hY:1≤y:= (R.alloy.B.a.fits.delayed _).le
   have hP:1 ≤ amplification R i μ:= coversQ _ _ |>.1

   have hZ := glyphBound (S) i; let fP:= Bq*y^(-((q+1:ℕ):ℝ)); let fp':= ψ*y^(-(q:ℝ)); have he': 0 ≤ ψ:= hZ.1.le; have hω:fp'≤1:= (mul_le_of_le_one_right he' (Real.rpow_le_one_of_one_le_of_nonpos hY (neg_nonpos.mpr (Nat.cast_nonneg _)))).trans hZ.2
   have hν: f≤fp':= hf.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (neg_le_neg (Nat.cast_le.mpr (q.le_succ)))) he') -- defeq ψ?

   have hk: κ⁻¹ * f ≤ fp' * ε:= by
       rw [inv_div, div_inv_eq_mul]; have hl:(ε*y)*fP=fp'*ε:=by
          rw [show fP=fp'*y⁻¹ from ?_]; field_simp
          unfold fP fp'; push_cast; rw [show (-((q:ℝ)+1) :ℝ) = -(q:ℝ) + (-1:ℝ) from by ring, Real.rpow_add hy, Real.rpow_neg_one, mul_assoc]
       exact (mul_le_mul_of_nonneg_left (show f≤fP from hf) (mul_nonneg he.le hy.le)).trans_eq hl
   let Q' : Throng.Hard.Pair M.K w (Ψ i).p.B (Ψ i).p.supportExponent (fp') ((fp')*ε):= Throng.Hard.Pair.mono _ (Origin.echoes hw D' u hb hK' hG') hν hk
   refine ⟨M.K, ⟨hQ, ?_, Throng.Hard.Pair.mono _ Q' hω (( (mul_le_mul_of_nonneg_right hω he.le).trans_eq (one_mul _) ).trans (le_mul_of_one_le_left he.le hP) )⟩, Q', fun t U=>?_⟩
   · exact Lamps.loan_monotone _ hx (mul_le_mul_of_nonneg_right (by rw [hp]; exact (coversQ _ _).2.2) he.le)
   let hL := Origin.reveals hw D' u hb h' hx t U; exact ⟨ hL.1, hL.2.2 ⟩
end Public
end Orbit
end Moonlight
end Sycamore
end YM.QuadraticLocal.Advent
