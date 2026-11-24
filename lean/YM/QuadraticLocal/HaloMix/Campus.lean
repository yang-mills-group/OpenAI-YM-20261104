import YM.QuadraticLocal.HaloMix.Queried
/-!
# Repetition (unassigned arity & positions scale) using same step weight book

Full MARK_POLY Rough product law without any fixed limit on global arity or
replica across terms! Rates on the complete bill & final canonical convention
for use downstream. Also works restricting the markers accordingly at every
stage. Before marker choices budgeting Ω only depends on k & p & schedule,
indeed available with any allowed sequence of Opportunity (can align with
sharp semesters). Pack down once per step, so close length cost is still
coupling-subpower (PaceR.Close). This does not ask for separation, but also
doesn't include converting radii back via separated hypothesis if used.

Input physical factor has fixed regulator `R.family` & model after actual
 calibration, enrollment before real tracking.S.S. No extra error perturbations
 needed on this Path. K and E holdings as in Reader.sizeable. For ANY torus, volume,
 and cutoff AFTER setup and trajectory choices. Occupancy charged on all x-support
 tests independent => stronger post budget; using this common hit norm instead of
 `sup_s EqJMtheta` implicitly paying both global units and ALL anchor costs through
 same price. If using a larger rooted-input estimate at stronger support exponents
 need to convert it with strengthened margin *before* this operation.
 Intermediate stages keep that stronger exponent & canopy receipts (not shrinking
 aperture of real fields, only cost wallet). No claims about witness for compiled
 sharp approximation or its suppliers after this rough propagation.

 Post growth budget in all query including deletion, not just magnitude of
 integrated density; path retains USUAL `.Scholar` levels and their canonical
 addresses, and every field payload and test tuple through output Price. Does not
 include any engineering boosts or reindex beyond projected-origin stencils.
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
abbrev Curriculum := (i:ℕ) → Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i)
noncomputable def arrange : Curriculum R:= fun i=>⟨0,R.alloy.B.a.clock.J i,step_paid S i,Nat.zero_le _,le_rfl, (by have h:= (R.alloy.B.a.clock.adm i); omega)⟩

variable (D0: Curriculum R)
def extent (i b:ℕ):ℝ:= ∏ j∈Finset.Ico i b,Moonlight.volume R D Q Q0 (D0 j) Uq
local notation "Ω'" j:max=> Moonlight.volume R D Q Q0 (D0 j) Uq
lemma chosen (j:ℕ):1≤ Ω' j:= by
   apply le_trans _ (Moonlight.stipulates R D Q Q0 (D0 j) Uq).1
   apply le_add_of_le_of_nonneg (le_add_of_nonneg_right (abs_nonneg _)); positivity
lemma realm (i b:ℕ): 1 ≤ extent R D Q Q0 Uq D0 i b:= Finset.one_le_prod fun i hi=> chosen ..
local notation "Ζ"=> extent R D Q Q0 Uq D0
lemma width : Ζ i b ≤ PaceR.roof R i b:= prod_le_prod (fun i _=>zero_le_one.trans (chosen ..)) (fun i _=> (Moonlight.stipulates R D Q Q0 (D0 i) Uq).2)
lemma extent_step (hb:i<b) : Ζ i b = (Ω' i)* Ζ (i+1) b:= by
   unfold extent; rw [← Finset.insert_Ico_add_one_left_eq_Ico hb, prod_insert]; simp
variable (w:θ→ℝ)
local notation "w_B"=> fun i=> Stoop.radius w (Ζ i b)
lemma width_step (hx:i<b) : Stoop.radius w (Ζ i b) = Stoop.radius (Stoop.radius w (Ζ (i+1) b)) (Ω' i):=by
   ext1 v; dsimp only [Stoop.radius]; rw [extent_step R D Q Q0 Uq D0 hx,div_div,mul_comm (Ω' i)]
open QuadraticLocal.Throng -- caution Hard
variable {V:Type}[DecidableEq V]{p:BudgetPoint}{A0 B0 Yp Yx z:ℝ}{Bρ:ℕ}
variable (hw:∀ i,0<w i)
local notation "pω"=> Stoop.radius w
include hw
lemma health (i b:ℕ)(v:θ): 0< Stoop.radius w (extent R D Q Q0 Uq D0 i b) v:= div_pos (hw v) (zero_lt_one.trans_le (realm ..))
lemma cold {n:Side}{X0: RG.Rep G n}{o:θ→Site n}{T:Type}(K: QuadraticLocal.Hard T X0.p X0.activities.forced X0.activities.K o J)(ht:1≤ z)(hb:Throng.Hard.Pair K w Bρ A0 B0 Yp): Throng.Hard.Pair K (pω z) Bρ A0 B0 Yp:= by
   let wX:= pω z; have he(v):0<wX v:= div_pos (hw _) (zero_lt_one.trans_le ht); have hm(t:Poly J) : Poly.price wX t≤Poly.price w t:= by
       refine Finset.sum_le_sum fun i _=> mul_le_mul_of_nonneg_right ?_ (norm_nonneg (t.part i)); by_cases h:i=J.quiet; subst i; simp; exact ( Stoop.shrink w i h hw ht ).trans (mul_le_of_le_one_left (Poly.worth hw _).le (inv_le_one_of_one_le₀ ht))
   obtain ⟨f,hf,hF,hG⟩:=hb.cashout; refine ⟨f,hf,fun i=> budget_mono (hF i) ?_ ?_,fun i=> budget_mono (hG i) ?_ ?_⟩
   · intro j; split; exact mul_nonneg (Poly.nonnegative he _) (Real.exp_pos _).le; exact le_rfl
   · intro j; split; exact mul_le_mul_of_nonneg_right (hm _) (Real.exp_pos _).le; exact le_rfl
   · intro j; split; exact mul_nonneg (Throng.Hard.active_nonneg he _) (Real.exp_pos _).le; exact le_rfl
   intro j; split; exact mul_le_mul_of_nonneg_right (hm ( GridRenewal.Rain.fresh (f j) )) (Real.exp_pos _).le; exact le_rfl
omit hw
-- roots and support geometry are actual projections held for EVERY permitted mode. no chart shortening interpreted here, physical displacement vs cover.
variable {Xℓ:θ→Type} [∀ i,AddCommGroup (Xℓ i)][∀ i,Module ℝ (Xℓ i)]
variable (Actors:∀ i,Set (Xℓ i))(uK:∀ i, Submodule ℝ (Xℓ i))
variable (o:(j:ℕ)→θ→Site (R.family.side j n))(Loc:(j:ℕ)→θ→Support (R.family.side j n))
local notation "L0" i:max=> Affinity.Collared ( Loc i ) Actors uK
local notation "Xa" i:max=> o i
local notation "T" i:max=> Estate (Affinity.Wallet Actors) (o i) (Ψ i) J
variable (hO:∀ i,m≤ i→i<b → o i= (R.family.path.levels.clock.op i n).ratio.parent ∘ o (i+1))
variable (hL:∀ i,m≤ i→i<b → Loc i=(fun j=> (Loc (i+1) j).image (R.family.path.levels.clock.op i n).ratio.parent))
variable {ε:ℝ}
local notation "App"=> Integration.LocalComparison.actualPush
-- curriculum broad.Target.Census ANY count, Holder constant ε announced (can pick Θ small)
local notation "Hi"=> ( (Ψ i).p )
local notation "Ha"=> ( (Ψ (i+1)).p )
local notation "τ₁"=> (Hi).supportExponent
local notation "Υ"=> ((γ)^(-(q:ℝ))* forcedDivisor Z i)* ε
structure Kin (i:ℕ) (Fq: T i) (w:θ→ℝ) (ε:ℝ) : Prop where
   hostel : (L0 i) (Ψ i) Fq.canvas
   light : Fq.canvas.E.Paid w (Ψ i).p.B (Ψ i).p.supportExponent ε
   nights : Throng.Hard.Pair Fq.canvas.K w (Ψ i).p.B (Ψ i).p.supportExponent 1 ε -- not taking off actual vacuum!
structure Pase (q i:ℕ)(V: T i) (K0: T (i+1)) (w:θ→ℝ)(ε:ℝ) :Prop where
   takes : ( L0 i ) (Ψ i) V.canvas
   billE : V.canvas.E.Paid w (Ψ i).p.B ( (Ψ i).p.supportExponent+1+1 ) ((Moonlight.volume R D Q Q0 (D0 i) Uq)*ε)
   stay : V.canvas.Pays w (Ψ i).p.supportExponent ((Moonlight.volume R D Q Q0 (D0 i) Uq)*ε) (Time.quoteHard S i R.kit.book (Ψ (i+1)).beta)
   lateLedger : Throng.Hard.Pair V.canvas.K w (Ψ i).p.B (Ψ i).p.supportExponent (Time.quoteHard S i R.kit.book (Ψ (i+1)).beta) ((((Φ (i+1))^(-(q:ℝ)))* (forcedDivisor Z i))*ε)
   transmits : ∀ t:Wallet Actors, V.canvas.density t= Integration.LocalComparison.actualPush Z N n i (K0.canvas.density t)
-- Notation Hygiene? `Hi etc` under binder shadow on `structure` params i not global, macro issue! watch.
local notation "FF"=> Pase (N:=N) R D Q Ψ Q0 Uq D0 Actors uK o Loc q
local notation "Kt"=> Kin R Ψ Actors uK o Loc
variable {Y':Estate ( Affinity.Wallet Actors ) (o b) (Ψ b) J}
variable (hq:q+1≤R.alloy.B.a.clock.J m)
lemma under (F0:T (i+1)) {s:θ→ℝ} (h:Kin R Ψ Actors uK o Loc (i+1) F0 s ε)(he:ε≤1): F0.canvas.Pays s (Ψ (i+1)).p.supportExponent 1 1:=by obtain ⟨a,b,c',-⟩:= h.nights.cashout; exact ⟨Lamps.loan_monotone _ h.light he,⟨a,b,c'⟩⟩
include hO hL hv hq g v
-- commute parents.Movement.Asset.F
variable (he:0≤ε) (he':ε ≤ Pavilion.closedRoom (R.alloy.B.a.clock.hatBeta b)) (hb:b≤N)
local notation "Tc" j:max=> T j
include hw he he' hb
variable [Nonempty (Affinity.Wallet Actors)]
lemma sold (hm:m≤ i)(hi:i<b)(x:T (i+1))(hx:(Kt) (i+1) x w ε): ∃ f:T i,(FF i f x w ε) := by
    have h': ε ≤ Pavilion.closedRoom γ:= he'.trans (Real.rpow_le_rpow_of_nonpos ( positive R (i+1) ) ( clock_mono R g hi ) (by norm_num : -(2/3:ℝ) ≤ 0))
    let Zp (p:θ→Site (R.family.side i n)) (Pq:θ→ Support (R.family.side i n)) := ∃ f:Estate ( Affinity.Wallet Actors ) p (Ψ i) J, Affinity.Collared Pq Actors uK (Ψ i) f.canvas ∧ f.canvas.E.Paid w (Hi).B (τ₁+1+1) ((Ω' i)*ε)∧ f.canvas.Pays w τ₁ ((Ω' i)*ε) wp∧ Throng.Hard.Pair f.canvas.K w (Hi).B τ₁ wp (Υ)∧∀ t,f.canvas.density t= App Z N n i (x.canvas.density t)
    obtain ⟨f,ht,hE,hF,hD,hZ⟩: Zp (o i) (Loc i) := by rw [hO _ hm hi,hL _ hm hi]; exact (Reader.sizeable R D Q π Γ Ψ v hm C Q0 (D0 i) Uq hv (lt_of_lt_of_le hi hb) Actors uK w (Loc (i+1)) x hw hx.hostel (hq.trans ((S).fits.mono hm)) he h' hx.light hx.nights) -- hw? x range? syntax
    refine ⟨f,ht,hE,hF,hD,hZ⟩
omit hO hL hv hq g v hw he he' hb
structure Chorus (ε:ℝ)(q s b:ℕ)(V': T b) (T' :∀ i,s≤ i→i≤ b→ (T i)) : Prop where
    height : s ≤ b
    owns : T' b height (le_refl _)= V'
    ticket : ∀ i (h:s≤ i)(hx:i≤ b), Kin R Ψ Actors uK o Loc i (T' i h hx) (Stoop.radius w (extent R D Q Q0 Uq D0 i b)) ε
    orders : ∀ i (h:s≤ i)(hx:i<b), ( Pase (N:=N) R D Q Ψ Q0 Uq D0 Actors uK o Loc q i ( T' i h hx.le ) ( T' (i+1) ( Nat.le_succ_of_le h ) hx ) ( Stoop.radius w (extent R D Q Q0 Uq D0 (i+1) b) ) ε ) -- carries ALL updated states pre-shrink and receipt.Plans.H
set_option linter.unusedSectionVars false
include hv v hw he
lemma ready {w':θ→ℝ} (hw':∀ i,0<w' i)(hQ:m≤ i)(ht:i<N)(z:T i)(x:T (i+1))(hvX:(FF i z x w' ε)): Kin R Ψ Actors uK o Loc i z (Stoop.radius w' (Ω' i)) ε:=by
    let F':= volume R D Q Q0 (D0 i) Uq; have hl:= chosen R D Q Q0 Uq D0 i
    have hx: (Φ (i+1))^(-(q:ℝ))* forcedDivisor Z i ≤ 1:=by
       let k:= forcedDivisor Z i; let d:= (glyphBound (S) i); exact (mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos ((R.alloy.B.a.fits.delayed _).le) (neg_nonpos.mpr (Nat.cast_nonneg q))) d.1.le).trans ((one_mul k).trans_le d.2)
    refine ⟨hvX.takes,(?_ : (Moonlight.volume R D Q Q0 (D0 i) Uq)⁻¹ * ((Moonlight.volume R D Q Q0 (D0 i) Uq)*ε) = ε) ▸ (Stoop.tighten w' _ hw' hl hvX.stay.budget),Throng.Hard.Pair.mono _ (Orbit.cold w' hw' z.canvas.K hl hvX.lateLedger) (pace_released R (hv.ready C) π Γ Ψ v hQ ht) ((mul_le_mul_of_nonneg_right hx he).trans_eq (one_mul ε))⟩ -- order fix
    rw [← mul_assoc,inv_mul_cancel₀ (show Moonlight.volume R D Q Q0 (D0 i) Uq≠0 from (zero_lt_one.trans_le hl).ne'),one_mul]
include hO hL hq g he' hb
set_option quotPrecheck false
local notation "P'"=> Chorus (N:=N) R D Q Ψ Q0 Uq D0 w Actors uK o Loc
lemma hall (Vb :T b)(hX : Kin R Ψ Actors uK o Loc b Vb w ε) (hi:m ≤ i) (hz:i≤ b) : ∃ T', Chorus (N:=N) R D Q Ψ Q0 Uq D0 w Actors uK o Loc ε q i b Vb T' :=by
   induction hz using Nat.decreasingInduction with
   | self=>
      let T' (i:ℕ) (h:b≤ i)(hr:i≤b): T i:= (Nat.le_antisymm h hr) ▸ Vb; refine ⟨T',le_rfl,rfl,fun i h hr=>?_,fun i hi hj=> by omega⟩
      have hF:= Nat.le_antisymm h hr; subst i; have hh:T' b h hr=Vb:=rfl; rw [hh,show pω (Ζ b b)=w from funext (fun i=> by unfold Stoop.radius extent; simp)]; exact hX
   | of_succ i hx ih=>
      have h0:= health R D Q Q0 Uq D0 w hw (i+1) b; obtain ⟨T',hT⟩:= ih (Nat.le_succ_of_le hi); obtain ⟨z,hZ⟩:= sold R g D Q π Γ Ψ v C Q0 Uq hv D0 (w_B (i+1)) h0 Actors uK o Loc hO hL hq he he' hb hi hx _ (hT.ticket _ le_rfl hx)
      let X' (j:ℕ)(hx:i≤j)(he:j≤b) : T j := if hp:i<j then T' j hp he else (le_antisymm hx (Nat.le_of_not_gt hp)) ▸ z
      have hh : X' i le_rfl hx.le=z:= dif_neg (by omega : ¬i < i); have hh' j (h:i<j)(hy:j≤b) : X' j h.le hy=T' j h hy:= dif_pos h
      refine ⟨X',hx.le,(hh' b hx le_rfl).trans hT.owns,fun j hj hz=>?_,fun j hj hz=>?_⟩
      · rcases eq_or_lt_of_le hj with hi'|hi'; · subst j; rw [hh, width_step R D Q Q0 Uq D0 w hx]; exact ready R D Q π Γ Ψ v C Q0 Uq hv D0 w hw Actors uK o Loc he h0 hi (lt_of_lt_of_le hx hb) z _ hZ -- args
        rw [hh' j hi' hz]; exact hT.ticket _ hi' hz
      rcases eq_or_lt_of_le hj with hi'|hi'; · subst j; rw [hh,hh' (i+1) (by omega) hz]; exact hZ
      rw [hh' j hi' hz.le,hh' (j+1) (by omega) hz]; exact hT.orders _ hi' hz
end Orbit
end Moonlight
end Sycamore
end YM.QuadraticLocal.Advent
