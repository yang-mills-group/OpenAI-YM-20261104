import YM.QuadraticLocal.Perspective.Weather
import YM.QuadraticLocal.HaloMix.Lotus
import YM.QuadraticLocal.HaloMix.Parade
/-!
# Actual epoch supplier of all-mark rough bounds

Per-site Hit costs at given budget (arbitrary Θ including even many unbounded
replicas per torus, with arbitrary testing of all masked and stenciled marks).
Numbers uniform on these cuts. Receives one Step with **relative-to-Θ**
precision and preparation. Budgets even before enlarging geometry or spending
sup@Π Physics: input supportExponent is exact (`Rep.p`). Output regular with
+2 reserve, strong K PROP budget at declared exponent. No claims of canonical
reads at high arity. Allows using arbitrary Opportunity for Frame.Owner.Policy,
Align logistics *not* supplied unless fits Provider.Cap.State.Tech.P_Frame.*

This proves quantitative broadcast *pre-engineering* over each full Θ array on
 actual Concourse even without center separation. Use growth estimate Moonlight
 to carry on rough radii across close UV region (stage power polynomial, x→any).
 Does not ask to keep the same rough radius after successive steps.Mono later.
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
local notation "δ"=> forcedDivisor Z i
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
abbrev volume := (Delay.fineMonitor G L xd)^(Pavilion.Degree D R.rolls Q R.kit.target φ Q0 R.alloy.delay Pt Uq)
-- Genuine polynomial in Monitor at stipulated stage and coupling. Use THIS power, not a looser super-polynomial from other Beaming calls, when publishing per-step radius changes.
local notation "Xn"=> R.metals.p.profile I
lemma stipulates : 1+(|Spire.fees L ((Xn).supportExponent+1+1)|)+|( salary ).enroll xd| * |(salary).price xd| ≤ Ω ∧ (Ω) ≤ Advent.budgetR R i:= by
    let hC:= Pavilion.live D R.rolls Q R.kit.target φ Q0 R.alloy.delay Pt Uq (Φ i) (R.alloy.B.valid.pays i); refine ⟨hC.now,?_⟩; unfold budgetR; rw [PriceCompiler.beta_eq R.alloy.B.valid i]; exact hC.horizon
local notation "fD"=> Time.forecastK S i (R.kit).scout
variable (r:i<N)
include hv r v l
private lemma eyes (U:Opera.Guide R.alloy.B R.kit.shape N i n (Ψ (i+1))) (ht:(Ψ (i+1)).beta ∈ Shoot.band R.alloy.B.a (i+1)) : Nonempty (Travel.Eyes U P↓ ( fD ((Ψ (i+1)).beta) /8 ) ((salary).price xd) ((salary).enroll xd) capDay Pt.count) := by
    let hZ := (later R π Γ Ψ v (show m≤ i+1 from by omega) r).truep.point; let he:=(later R π Γ Ψ v l r.le).truep.point; have ha:= PriceCompiler.beta_eq R.alloy.B.valid i
    obtain ⟨hM,hF,hZ',hG,hL,hW,hW',hg⟩:= zones D Q A F hv.station.pledge (m:=i);
    unfold Time.forecastK; rw [ha]; obtain ⟨Eye,hE⟩:= (hv.education.enrolled _ _ Pt xd ( R.alloy.B.valid.pays i )).real _ _ _ _ ( Opera.protocol _ r R.kit.pledging.conducts.full ) (Ψ (i+1)) (Ψ i) _ U (ha ▸ trial_in ht) (hZ.symm ▸ hZ') (he.symm ▸ hF) (he.symm ▸ rfl) (hZ.symm ▸ he.symm ▸ hW') (he.symm ▸ rfl); exact ⟨Eye⟩
-- price conversions
local notation "fi"=> (Ψ (i+1)).beta
omit hv r v l
open RemainderComparison
local notation "E"=> RG.Shoot.band
local notation "Υ"=> (Halo.hike (R.kit.target Y I) (Φ i) (Fintype.card (Site L)))
local notation "νζ"=> (salary).enroll (Φ i)
local notation "ΓM"=> (salary).price (Φ i)
variable {fY Ecap:ℝ}(he:0<Ecap)(hS:Ecap≤ Pavilion.closedRoom (R.alloy.B.a.clock.hatBeta (i+1)))
local notation "ζm"=> raiseRoom (γ) / Ecap
local notation "Ψm"=> (νζ*Ecap)⁻¹
local notation "X₁"=> (Xn).supportExponent
local notation "fee"=> Spire.fees L (X₁+1+1)
-- numerical only.World.h.X. Need on real U. Anchor heights receipt ≡ Rep.p=budget Weather.
include Uq he hS
set_option maxHeartbeats 450000
lemma affords (hs:1 ≤ ((salary).enroll (Φ i))) :
     2*(Ecap+1) ≤ capDay ∧ 1 ≤ (Ψm) ∧ (νζ*(Ψm))*(2*(Ecap+Ecap)) ≤ capDay ∧ 1 ≤ (ζm) ∧ (ζm)*(2*(Ecap+Ecap)) ≤ capDay ∧ Υ ((ζm)*(2*(Ecap+Ecap))) ≤ Daisy.ribbon (R.kit.target Y I) L (Φ i) ∧ fee*Ecap+(Ψm)⁻¹*ΓM ≤ volume R D Q Q0 Pt Uq*Ecap:=by
    let kΩ:= Pavilion.Degree D R.rolls Q R.kit.target φ Q0 R.alloy.delay Pt Uq; let hC:= Pavilion.live D R.rolls Q R.kit.target φ Q0 R.alloy.delay Pt Uq (Φ i) (R.alloy.B.valid.pays i)
    let ha:= hC.positive; change 1 < betaF G (Φ i) L at ha; rw [← PriceCompiler.beta_eq R.alloy.B.valid i] at ha
    let θ':= Ψm; let y:= γ; have hy:0<y:=zero_lt_one.trans ha; let K':= ζm
    have hX: 0< (νζ):= zero_lt_one.trans_le hs
    have hc:= Real.rpow_le_rpow_of_exponent_le (show 1≤y from ha.le) (show -(2/3:ℝ)≤ -(1/2:ℝ) from by norm_num)
    have hS : Ecap ≤ raiseRoom y:= hS.trans hc
    have hh: raiseRoom y ≤1:= Real.rpow_le_one_of_one_le_of_nonpos ha.le (by norm_num: -(1/2:ℝ) ≤ 0)
    have he' : Ecap≤1:= le_trans hS hh;
    have hid: K'*(2*(Ecap+Ecap))= 4*raiseRoom y:= by unfold K' y; field_simp; ring
    refine ⟨?_,?_,?_,(le_div_iff₀ he).mpr (by rwa [one_mul]),hid.trans_le ?_, ?_,?_⟩
    · change 2*(_+1) ≤ 16; linarith
    · apply one_le_inv₀ (mul_pos hX he) |>.2
      have hz:= hC.cap; rw [← PriceCompiler.beta_eq R.alloy.B.valid i] at hz; change νζ*Ecap≤1; rw [abs_of_pos hX] at hz; refine (mul_le_mul_of_nonneg_left (by assumption : Ecap ≤ closedRoom y) hX.le).trans hz
    · have hz : (νζ*(Ψm))*(2*(Ecap+Ecap))=4:= by field_simp; norm_num
      rw [hz]; norm_num [capDay]
    · change 4*(_ : ℝ) ≤16; linarith
    · rw [show ζm*(2*(Ecap+Ecap))=_ from hid]; unfold y; rw [PriceCompiler.beta_eq R.alloy.B.valid i]; exact hC.hectare -- hid y unfolded?
    have hs₁ : fee+(νζ)*ΓM ≤ Ω:= by
       apply le_trans _ hC.now; unfold front; change _ ≤ (1+|fee|)+ |νζ| * |ΓM|
       rw [abs_of_pos hX]; exact add_le_add ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) (mul_le_mul_of_nonneg_left (le_abs_self _) hX.le)
    rw [inv_inv]; exact le_trans (le_of_eq (show fee*Ecap+νζ*Ecap*ΓM=(fee+νζ*ΓM)*Ecap from by ring)) (mul_le_mul_of_nonneg_right hs₁ he.le)

include v l hv r
local notation "kD"=> forcedDivisor Z i
-- separate Φ uncertainty.H.L; compute quoteR marked hit ≤ sharp with explicit y factor sqrt.
omit Uq hS in
lemma performance {q:ℕ}(ht:q+1 ≤ R.alloy.B.a.clock.J i):
    (ζm)⁻¹* wp ≤ γ ^(-(q:ℝ))*( forcedDivisor Z i ) * Ecap:= by
    have hY:1≤ γ:= (R.alloy.B.a.fits.delayed (i+1)).le; let y:=(Φ (i+1)); let hh:= force_bill R (hv.ready C) π Γ Ψ v l r ht; have hz:= mul_nonneg ( Real.rpow_nonneg (zero_le_one.trans hY) (-( ((q+1:ℕ):ℝ) )) ) (( glyphBound (S) i ).1.le)
    have hy:0<y:=zero_lt_one.trans_le hY; have hp:0<raiseRoom y:=Real.rpow_pos_of_pos hy _; have hn: (raiseRoom y)⁻¹≤y:=by rw [show (raiseRoom y)⁻¹= y^(1/2:ℝ) from ?_]; apply (Real.rpow_le_rpow_of_exponent_le hY (show (1/2:ℝ) ≤ 1 from by norm_num)).trans_eq (Real.rpow_one y); rw [raiseRoom,Real.rpow_neg hy.le,inv_inv]; -- order
    let d:= kD; let w:=wp; calc
       _ = Ecap * ( (raiseRoom y)⁻¹ ) * w:=by unfold w; rw [inv_div,div_eq_mul_inv]
       _ ≤ Ecap * y * ( y^(-(↑(q+1:ℕ):ℝ))* d):= (mul_le_mul_of_nonneg_left hh (by positivity: 0≤ Ecap*(raiseRoom y)⁻¹)).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn he.le) hz)
       _ = _ := by
          have ht : y*(y^(-(↑(q+1:ℕ):ℝ)))= y^(-(q:ℝ)):= by
             nth_rw 1 [← Real.rpow_one y]; rw [← Real.rpow_add hy]; congr 1; push_cast; ring

          change _= y^(-(q:ℝ))*d*_; rw [mul_assoc Ecap,← mul_assoc y,ht,mul_comm]
-- Continuation.Owner.This is Cl contour. Head Root ∀ finite etc.
variable {Xℓ:θ→Type} [∀ i,AddCommGroup (Xℓ i)][∀ i,Module ℝ (Xℓ i)]
variable (Actors:∀ i,Set (Xℓ i))(uK:∀ i,Submodule ℝ (Xℓ i))
variable (w:θ→ℝ) {o:θ→Site (R.family.side (i+1) n)} (Loc:θ→Support (R.family.side (i+1) n))
variable (V : Estate (Affinity.Wallet Actors) o (Ψ (i+1)) J)
local notation "T"=> V.canvas
local notation "x'!"=> (τ).ratio.parent
local notation "Xr"=> (fun i=> (Loc i).image (τ).ratio.parent)
local notation "r'"=> (τ).ratio.parent ∘ o
variable (hq:q+1≤ (R.alloy.B.a.clock.J i))
variable (hw:∀ i,0<w i)(hX:Affinity.Collared Loc Actors uK (Ψ (i+1)) V.canvas)
variable (hx: V.canvas.E.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent Ecap)
variable (hM: Throng.Hard.Pair V.canvas.K w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent 1 Ecap)
variable [Nonempty (Affinity.Wallet Actors)]
local notation "Ω'p"=> volume R D Q Q0 Pt Uq
local notation "Y₁"=> Ψ i
include hw hx hM hX hq
open Affinity
set_option maxHeartbeats 720000
set_option maxRecDepth 5000
lemma aster : ∃ (V': Estate (Affinity.Wallet Actors) ((R.family.path.levels.clock.op i n).ratio.parent ∘ o) (Ψ i) J), Affinity.Collared Xr Actors uK (Ψ i) V'.canvas ∧ V'.canvas.E.Paid w (Ψ i).p.B ((Ψ i).p.supportExponent+1+1) ( volume R D Q Q0 Pt Uq*Ecap ) ∧ V'.canvas.Pays w (Ψ i).p.supportExponent ( volume R D Q Q0 Pt Uq*Ecap ) wp ∧ Throng.Hard.Pair V'.canvas.K w (Ψ i).p.B (Ψ i).p.supportExponent wp (γ ^(-(q:ℝ)) * kD * Ecap ) ∧ ∀ t, V'.canvas.density t= Integration.LocalComparison.actualPush Z N n i ((T).density t):=by
    let φ₁:= (τ); obtain ⟨U,hU,⟨WC⟩⟩:=(v.2 i l r).earns; let P':= (Ψ i); let Pq:= (Ψ (i+1)); let z:=(τ).ratio.parent
    have hL:= (later R π Γ Ψ v (Nat.le_succ_of_le l) r); have hr:= (later R π Γ Ψ v l r.le)
    have ht: Pq.beta∈ Shoot.band S (i+1):= (hL.beta.symm ▸ (R.T.sticks N n|>.prices _ (Nat.zero_le _) r).2)
    obtain ⟨v0⟩:= eyes R D Q π Γ Ψ v l C Q0 Pt hv r U ht; obtain ⟨T',Sh⟩:= Throng.certificates (T) hx hM; obtain ⟨hE,hY,hΩ,hβ,hν,hK,hV⟩:= affords R D Q Q0 Pt Uq he hS v0.bells.allowed
    let α:= Classical.arbitrary (Affinity.Wallet Actors); let B0:= Fintype.card θ; let σ:= Ψm; let q0:=ζm;
    have ha : (τ).ratio.count=L:= U.laws.data.funds.length_eq; have hp : P'.p.supportExponent= (Xn).supportExponent:= (congr_arg BudgetPoint.supportExponent hr.truep.point).trans (congr_arg RG.Stage.supportExponent (PriceCompiler.params_eq R.alloy.B.valid i))
    have hΦ := (v.1.visit i l r).ident; have hΦ':∀ x', (Ψ i).eval x' ≠ 0:= fun U'=> (congr_fun hr.view U').symm ▸ (YM.Multi.AxisShift.chosen_positive R.makes.wilson r.le U').ne'
    have hx':= spare R π Γ Ψ v (Nat.le_succ_of_le l) r; have hC(u:J.Mode): u.val.card≤B0:=Finset.card_le_univ _
    let f':= Travel.Parade.roster U WC v0 Actors uK T w T' hw hx' hC hE α Sh hY hΩ hβ (ha.symm ▸ hK) Loc hX
    haveI:= Travel.countF U T w T' hw hx' α
    obtain ⟨hy,hf,hX',hΛ,hω⟩:= Travel.Parade.present U WC v0 Actors uK T w T' hw hx' hC hE α Sh hY hΩ hβ hν (ha.symm ▸ hK) Loc hX (Willow.spare_pos _).le hΦ' hΦ (Classical.choice (Tree.select (τ).ratio ((τ).patch.odd_side)))
    let A':= Spire.fees (τ).ratio.count (P'.p.supportExponent+1+1)*Ecap+σ⁻¹*ΓM; have hΓ:A'≤ volume R D Q Q0 Pt Uq *Ecap:= by unfold A'; rw [hp,ha]; exact hV
    refine ⟨{ canvas:=f',locale:=_,seats:=inferInstance},hy,Lamps.loan_monotone _ hf hΓ,⟨ Lamps.loan_monotone _ hX'.budget hΓ,hX'.wages ⟩,Throng.Hard.Pair.mono f'.K hΛ le_rfl ?_,fun t=>?_⟩
    · exact performance R D Q π Γ Ψ v l C Q0 hv r he hq
    unfold Integration.LocalComparison.actualPush; rw [show R.family.path.β N n (i+1)= (P).beta from hL.beta.symm]; exact (hω t).symm
end Moonlight
end Sycamore
end YM.QuadraticLocal.Advent
