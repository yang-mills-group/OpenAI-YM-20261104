import YM.QuadraticLocal.Expo
import YM.QuadraticLocal.Found.Cross
import YM.QuadraticLocal.Display
import YM.QuadraticLocal.Pry
import YM.Next.MULTISOURCE.Determined
/-!
# Runner — certify an entire marked recurrency availability at true history

Inputs bought (`Run.attain`), at each allowed PERIOD, all fixed polynomial markers through L, not
assuming positivity except what the Run supplies. Exponent alignment to actual.Stencil orientation
chip & clip payments. Exact `Op.push` NOT multiplying by covariance denominators after.Yet
keeps regular log errors for later: this file pays *whole* knob, roots. Outputs rough valuation per
unit load. No tilting on off-good densities or claim about formal correspondence here. Caller
supplies actual campaign and doesn't reselect.

Separate `Treasure.Letter`, issue q's with universal stages.
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
include v l -- defs costs measured at THAT Concourse; convenience implicit variables in appearance
lemma later (r:i≤N) : Appearance A Ta (π i) i n N k P':= v.1.walk _ l r -- l automatic?
-- use as actual push instance.L.N. preserve direct `β`.
include l
lemma cards (r:i≤N) : ∃ x:Carrier Z N n i,x.rep=P':=by
    have hp:= (later R π Γ Ψ v l r); have hc:= hp.truep; have hb:=(R.T.sticks N n|>.prices _ (Nat.zero_le _) r).1
    exact ⟨⟨P',hc.path.trans hb.path.symm,hc.clip.trans hb.clip.symm,hc.point,hp.view⟩, rfl⟩
def avatar (r:i≤N): Carrier Z N n i:=
  { rep:= P'
    path:= ((v.1.walk i l r).truep).path.trans ((R.T.sticks N n|>.prices _ (Nat.zero_le _) r).1.path).symm
    clip:= ((v.1.walk i l r).truep).clip.trans ((R.T.sticks N n|>.prices _ (Nat.zero_le _) r).1.clip).symm
    point:= (v.1.walk i l r).truep.point
    vacuum:= (v.1.walk i l r).view } -- l isn't parameter v fields binder metan notation ok?
lemma spare (r:i≤N) : HasSlots (P').p (P').activities:=by
    have ht:= (later R π Γ Ψ v l r).truep; have h' : R.alloy.B.bake.retain N i n P':=ht.loads
    rw [R.kit.machine.ready] at h'
    rw [ht.point]; exact (PeriodFuture.pockets h').2.2.2.2
variable (r:i<N)
include r
local notation "κ"=> forcedDivisor Z i -- args wrong
include h in
lemma force_bill (hq:q ≤ R.alloy.B.a.clock.J i) : Time.quoteHard S i (R.kit.book) (P).beta ≤ ((Φ (i+1))^(-(q:ℝ)))*forcedDivisor Z i:=by
    have hh':= h.frost.bears _ _ _ (step_paid S i) (R.alloy.B.valid.pays i)
    let f:= (P).beta; have he : f= (R.T.history N n (i+1)).beta:= (later R π Γ Ψ v (show m≤ i+1 from by omega) r).beta; have ha:= PriceCompiler.beta_eq R.alloy.B.valid i
    have hez: Next.Scheduling.inBand (Φ (i+1)) f :=by rw [he]; exact trial_in (R.T.sticks N n|>.prices _ (Nat.zero_le _) r).2
    unfold Time.quoteHard; rw [ha]; exact Beaming.Leg.pretty hh' q hq f (ha ▸ hez)
variable (d : ℕ)
-- d HEIGHT arbitrary.K budgets supplied when requested d, not by assuming occupancy etc.
local notation "Ĉ"=> R.alloy.B.a.clock
local notation "B0"=> Beaming.Leg
local notation "ω₀"=> R.rolls.L Y
local notation "q₀"=> R.kit.book Y I
local notation "o₀"=> R.kit.shape.o Y I
local notation "A₀"=> R.kit.scout Y I
local notation "πτ"=> R.kit.walls Y I
local notation "Q'"=> R.kit.target Y I
local notation "µ"=> R.kit.shape.μ Y I
open Travel
variable (U:Opera.Guide R.alloy.B R.kit.shape N i n (Ψ (i+1))) -- R.alloy.B error notation
local notation "θ"=> ((P').p.supportExponent+1+1)
local notation "ϕ"=> Spire.fees L θ
local notation "œ"=> Beaming.grain I
include h K₀ in
lemma invited {U₁ V:ℝ→ℝ} {kx:ℕ} (hT:Beaming.RoomR Q' L µ xd πτ q d kx œ q₀ A₀ o₀ U₁ V): ∃ Eye:Eyes U P' (wa / 8) (V xd) (U₁ xd) 4 q, Eye.height=d:=by
   let T' := R.alloy.B.a; obtain ⟨hM,hF,hZ,hG,hZ',hW,hW',hg⟩:= zones D Q A F K₀.pledge (m:=i)
   have hPz:= (later R π Γ Ψ v (show m≤ i+1 from by omega) r); have hz:= hPz.truep.point; have he:= (later R π Γ Ψ v l r.le).truep.point; have ha:= PriceCompiler.beta_eq R.alloy.B.valid i
   have ht:(P).beta ∈ Shoot.band S (i+1):= (hPz.beta.symm ▸ (R.T.sticks N n|>.prices _ (Nat.zero_le _) r).2)
   unfold Time.forecastK; rw [ha]; exact hT.summer _ _ _ _ (Opera.protocol _ r (R.kit).pledging.conducts.full) _ _ _ U (ha ▸ trial_in ht) (hz.symm ▸ hZ) (he.symm ▸ hF) (he.symm ▸ rfl) (hz.symm ▸ he.symm ▸ hW') (he.symm ▸ rfl)
section payroll
variable {α I' Θ': Type}[DecidableEq Θ']{J : Marker.Census Θ'} {o:Θ'→ Site (R.family.side (i+1) n)}(w:Θ'→ℝ) (hw:∀ v,0<w v)
variable (Λ:Gallery α I' o (Ψ (i+1)) J)(hh:Λ.Pays w ((Ψ (i+1)).p.supportExponent) 1 1)
variable (hℓ:q ≤ R.alloy.B.a.clock.J i)
local notation "τφ"=> (R.alloy.B.a.clock.op i n)
local notation "o'"=> ((τφ).ratio.parent) ∘ o
include v h l r K₀
variable [Countable I'] [Nonempty α][Fintype Θ']
variable (hq:∀ u:J.Mode,u.val.card≤q)
local notation "spray"=> Beaming.spray
local notation "Ơ"=> spray (Φ (i+1))
-- request Eye for any q on this level. Caller can specialize D height.
include hw Λ hh hℓ hq
lemma growth : ∃ (S' :Type)(Λ': Gallery α S' ((R.family.path.levels.clock.op i n).ratio.parent ∘ o) P' J), Countable S' ∧ Λ'.Pays w ((Ψ i).p.supportExponent) (min (spray (Φ (i+1))) ((Φ (i+1)) ^ (Beaming.grain I))) wp ∧ (∀ x, Λ'.density x= Integration.LocalComparison.actualPush Z N n i (Λ.density x)) :=by
   obtain ⟨U,hU,⟨WC⟩⟩:= (v.2 i l r).earns; obtain ⟨Wq,y,bω,hT⟩:= h.frost.license _ _ (step_paid S i) q I hℓ le_rfl (show 1≤ I from (by have hm:= (S).clock.adm i; omega))
   let P₁:=hT (Φ i) (R.alloy.B.valid.pays i); obtain ⟨E,he⟩:= invited R h D Q π Γ Ψ v K₀ l r I U P₁; let Wχ:= bω; obtain ⟨w'⟩:= Travel.sealed Λ w hh; have hx:= spare R π Γ Ψ v (show m≤ i+1 from Nat.le_succ_of_le l) r
   let θ' := (Classical.arbitrary α); have hX:= (later R π Γ Ψ v (Nat.le_succ_of_le l) r); have hy:=(later R π Γ Ψ v l r.le); have hP: (P').eval=(τφ).push (P).beta (P).eval := (v.1.visit i l r).ident; have hP' : ∀ U',(P').eval U'≠0:= fun U'=> (congr_fun hy.view U').symm ▸ (YM.Multi.AxisShift.chosen_positive R.makes.wilson r.le U').ne'
   let s' := (Travel.Names U Λ w w' hw hx θ' (k:=q)); let Λ':Gallery α s' ((R.family.path.levels.clock.op i n).ratio.parent ∘ o) P' J:= Travel.outcome U WC E Λ w w' hw hx hq (by norm_num) θ'
   obtain ⟨hb₁,hB₁⟩:= Travel.passed U WC E Λ w w' hw hx hq (by norm_num) θ' (Willow.spare_pos _).le hP' hP (Classical.choice (Tree.select (τφ).ratio ((τφ).patch.odd_side)))
   let X' := Spire.fees ((τφ).ratio.count) θ+(y (Φ i))^q*Wχ (Φ i); have hΞ : Λ'.Pays w ((P').p.supportExponent) X' wp := by rw [mul_one] at hb₁; exact hb₁
   refine ⟨s',Λ',Travel.counting U Λ w w' hw hx θ' (k:=q),⟨?_,hΞ.wages⟩, fun x=>?_ ⟩
   · apply Lamps.loan_monotone _ hΞ.budget (le_min ?_ ?_)
     all_goals unfold X'; rw [show (τφ).ratio.count=L from U.laws.data.funds.length_eq, show (P').p.supportExponent=(R.metals.p.profile (I)).supportExponent from (congr_arg BudgetPoint.supportExponent (show (Ψ i).p=X from hy.truep.point)).trans (congr_arg RG.Stage.supportExponent (PriceCompiler.params_eq R.alloy.B.valid i)),PriceCompiler.beta_eq R.alloy.B.valid i]
     · exact P₁.geom.trans P₁.growth
     exact P₁.lightBand
   unfold Integration.LocalComparison.actualPush; rw [show R.family.path.β N n (i+1)= (P).beta from hX.beta.symm]; exact (hB₁ x).symm
end payroll
end YM.QuadraticLocal.Advent
