import YM.QuadraticLocal.Union.Return
import YM.QuadraticLocal.Relative.Pair
import YM.QuadraticLocal.Earn.Temp
/-!
 # One step at the original marker currency w — exact cost of temporary packing

 Shows explicit step-polynomial and certified attenuations from Page.Uses.
 Requires earned budgets on α (NOT assuming anything about *number* of radius locations
 beyond the paid input and the mode arity cap). If there is polynomial in small prerequirements
 for Art.Height_T.Param.Clock borrower*, may still cost polynomial of previous coupons on rebound.
 Reserve. Consumer chooses exact kernel inputs beforehand, w resonance and SenseRead.
 No Φ projection yet to match older or arrived readout, nor Kant positivity for full.T.
 No unbounded-copy use. Explicit pole quiver makes the specific hypotheses of construction working.
 This supplies strong-ish K priced reserve ratio after weighted shrink. Need compare with requested
 OUTPUT inverse κ.Ph converted form through all uses; keep `B-beyond` unnormalized fits
 as separate vendor and multiplier. 
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
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
local notation "Ep"=> Episode H Mutation -- ignore
open Integration.LocalComparison VowsR QuadraticLocal.Mentor
variable {φ:ℕ→ℕ} (C:VowsR.LawScroll G φ) (Q0:QuadraticLocal.Mentor.Offices.Books D R.rolls Q φ)
variable (Y':VowsR.Chamber C R.kit D Q Q0)
local notation "pE"=> Y'.education
local notation "hZ"=> Y'.station.pledge
local notation "hr"=> Y'.ready C
variable (hℓ:m≤ i) (hz: i<N)
local notation "ℓ"=> (R.alloy.B.a.S.oneStep i n).exact_size
variable (Pt:QuadraticLocal.Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
variable (X': Card R.rolls D (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i) (R.alloy.B.a.clock.adm (i+1)) (Burn.horizon k)) (hP:Journey D R.alloy (m:=i) (N:=N) X')
local notation "hx"=> (show Burn.horizon k+2≤R.alloy.B.a.clock.J i from hk.trans ((S).fits.mono hℓ))
namespace Oak
variable (V₁: Lesson (N:=N) R hk D Q π Γ hℓ)
variable (V₂: Oak.Calendar R hk D Q π Γ Ψ hℓ (N:=N) V₁)
local notation "k0"=> V₁.entry
local notation "E!"=> (Oak.era R hk D Q π Γ hℓ Pt V₁)
local notation "G'"=> ( Coat.gStep (P).beta )
local notation "k'"=> Φ (i+1)
local notation "FY"=> Burn.young γ k
open RemainderComparison
variable (Qa: Mentor.Forecast D R.rolls Q φ Q0)(hQ:MintClock.Hospital D R.rolls Q R.kit.target φ Q0 Qa R.alloy.delay)
variable {Θ ι ιw α : Type} [Fintype Θ][DecidableEq Θ]{R₀: Marker.Census Θ}
variable {K₁:Earn.Passport (R.family.side (i+1) n) Θ}
variable {W': Θ→Type} [∀ i,AddCommGroup (W' i)][∀ i,Module ℝ (W' i)]
variable (Actors:∀ i, Set (W' i))(U:∀ i,Submodule ℝ (W' i))
variable (M:ι→ Earn.Row K₁ R₀ G ( Affinity.Wallet Actors )) (Z₁:Tint.Incoming K₁ (Ψ (i+1)) (Affinity.Wallet Actors) ιw R₀)
variable (w:Θ→ℝ)(ηL:Θ→ℕ)
local notation "ζ1"=> (Ψ i).p.supportExponent
open Cruise.Semester
local notation "S*"=> Pane.panel A i (ℓ)
local notation "Xn"=> ( S* )
-- no undocumented Φ viability required.Health.T.Art. Universe Hobby interior entire.F.No.
local notation "µ"=> (R.family.path.levels.clock.op i n).ratio
local notation "F₀"=> Cruise.publish
local notation "F₁"=> (φ)
variable (jJ Vh:ℕ)
variable (Vₜ:Mentor.Cruise.Voter M (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) jJ Pt.count Pt.stage k (R.alloy.B.a.clock.J i))
local notation "uP"=> ( Mentor.Cruise.publish D R.rolls Q A φ Q0 Pt (E!) (ℓ) M jJ Vₜ k0)
local notation "θρ"=> ( Mentor.Cruise.funded D R.rolls Q A φ Q0 Pt (E!) (ℓ) M jJ Vₜ k0 V₁.studied Qa)
-- preserve field.Forecast Blueprint LP.Age.P.Region.Day.Real.Supplier.Op_L_kernel coupling.W.Em.K_Frame_st. keep ANY qTerm.HorrowMaker.CountLoan `jJ`.
local notation "S✔"=> ( Mentor.Cruise.Semester.successor D R.rolls Q A φ Q0 Pt E! (ℓ) M jJ Vₜ k0 V₁.studied Qa)
local notation "B*"=> (Ψ (i+1)).p.B
local notation "κP"=> (K₁.coarser µ)
-- allow µ.Public alias L.Photo.ItemClock.A.Kernel.Run venue. 
local notation "Φout"=> (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J i))
local notation "xΨ"=> Page
local notation "Ω"=> Oak.expenseReal R hk D Q π Γ Q0 hℓ Pt V₁ Qa jJ Vh
local notation "pΩ"=> Oak.figureReal R hk D Q π Γ Q0 hℓ Pt V₁ Qa jJ Vh
-- e-bound at normalized mark prices after actor arity packing.Frame.Pl.Q.Erank before masks.
variable (e_E c_P:ℝ) (heCp:c_P ≤ (Oak.expenseReal R hk D Q π Γ Q0 hℓ Pt V₁ Qa jJ Vh)⁻¹)
-- max count. true layout hypotheses on row identity.Actor.Metadata.LabelSource.Policy
variable (hJ: Pt.count ≤ Burn.horizon k+2)(hv: Vh ≤ R.alloy.B.a.clock.J i)
variable (Yv: Earn.Scene.Armada M w ηL (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) c_P jJ Pt.count Vh)
variable (hM:Earn.Tableau U Actors M)(y: Affinity.Wallet Actors)[Countable ι][Countable ιw]
variable (hL: Affinity.Taut K₁.support Actors U Z₁.old)(hY: Affinity.Crown K₁.support Actors U Z₁.hard)
variable (hO:Z₁.old.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent e_E)(hP₁:Z₁.hard.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent 1)
local notation "bP"=> (Mentor.Tuition.need jJ (Tolerance I))
local notation "tΩ"=> (Oak.student (n:=n) R hk D Q π Γ Q0 hℓ Pt V₁ Qa Actors M jJ Vₜ)
local notation "rΩ"=> Ω^5
local notation "Ψp"=> (Ψ (i+1)).beta
local notation "ζc"=> ((pΩ).hitPrice G (µ).count (P).p (P').p c_P e_E FY G')
local notation "Θ'"=> (Mentor.Tuition.need jJ (Tolerance I))
include v g hz hQ hℓ hk D Q C Y' V₂ hJ hv Yv hM y hL hY hP₁
-- price.FullBudget after transport operational Sem ∀.Sect.Prop.Measure.Edge.Height.S
variable (Sx:Set Θ)
variable (hClean:(Deletion.sink Sx Z₁.old).Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent e_E)(hFull:Z₁.old.Paid w (Ψ (i+1)).p.B (Ψ (i+1)).p.supportExponent 1)
include Sx Z₁ w hClean hFull
include heCp in
lemma companions (h0:0< e_E)(hh:e_E≤1): ∃ ξ : Type,Countable ξ ∧ ∃ U':Tint.Incoming κP P' (Affinity.Wallet Actors) ξ R₀, Earn.Scene.Armada tΩ w ηL Φout ((pΩ).produce (µ).count*c_P) jJ Pt.count Vh ∧ Earn.Tableau U Actors tΩ ∧ Affinity.Taut ((K₁.coarser µ).support) Actors U U'.old ∧ Affinity.Crown (κP).support Actors U U'.hard ∧ U'.old.Paid w (P').p.B ( (P').p.supportExponent+1+1 ) (ζc+(3*Ω+Ω^2)) ∧ (Deletion.sink Sx U'.old).Paid w (P').p.B ( (P').p.supportExponent+1+1 ) ζc ∧ U'.hard.Paid (Stoop.radius w rΩ) (P').p.B ((P').p.supportExponent) wp ∧ (∀ k:Affinity.Wallet Actors, Integration.LocalComparison.actualPush Z N n i ((Tint.Patrol.picture M Z₁).density k)=(Tint.Patrol.report tΩ U' G').density k) ∧ Earn.Earnings.Cashier pΩ G (µ).count (P).p (P').p Ω y₀ G' ∧ Ω ≤ budgetR R i ∧ ζc ≤ 8*Ω*(e_E+FY+ ((pΩ).fidelity)) := by
 let YH := V₂.clock; let Y₀:= Yv.positive; let f:= V₂.seeds; let ℓ₀ := R.rolls
 have hf:= later R π Γ Ψ v (Nat.le_succ_of_le hℓ) hz; have hp':= later R π Γ Ψ v hℓ hz.le
 have hp: (P').eval= (Xn).push (Ψ (i+1)).beta (P).eval:= (v.1.visit _ hℓ hz).ident
 have hz' : ∀ U',(P').eval U' ≠ 0 := fun U'=> (congr_fun hp'.view U').symm ▸ (YM.Multi.AxisShift.chosen_positive R.makes.wilson hz.le U').ne'
 obtain ⟨ι',hI,Υ,hΨp,hCL,hH,hθ,hActor,hZ',hF',hY',h_u,h_r,hA⟩:= Mentor.Cruise.Semester.peers D R.rolls Q A F φ Q0 hZ pE Pt E! (ℓ) Actors U M w ηL jJ Vₜ V₁.entry V₁.studied Qa hf.truep.point (hf.truep.path.trans (congr_fun (congr_fun R.alloy.B.bases N) (i+1))) Z₁ Yv.positive (spare R π Γ Ψ v (Nat.le_succ_of_le hℓ) hz) y YH V₂.seeds hp'.truep.point hQ hJ Vh hv (hf.beta.symm ▸ (R.T.sticks N n|>.prices _ (Nat.zero_le _) hz).2) hz g (n:=n) rfl ( Oak.parcel R hk D Q π Γ Ψ v C Q0 Y' hℓ hz V₁ V₂ ) c_P Yv heCp h0 hh hP₁ V₂.itinerary hM hL hY Sx hClean hFull (Classical.choice (Tree.select (τ).ratio (τ).patch.odd_side)) (Or.inl ⟨hz',hp⟩)
 refine ⟨ι',hI,Υ,hZ',hA,h_u,h_r,hΨp,hCL,hH,fun k=>?_,hF',hY',hθ⟩
 unfold Integration.LocalComparison.actualPush; rw [show R.family.path.β N n (i+1)= (P).beta from hf.beta.symm]; exact hActor k

namespace Buffered
open Earn
local notation "w₁"=> Stoop.radius w (Ω)
local notation "ξ₁"=> Ω⁻¹*c_P
local notation "eτ"=> Ω⁻¹*e_E
local notation "rμ"=> Pt.count
local notation "X₁"=> Earn.Earnings.hitPrice pΩ G (µ).count (P).p (P').p ξ₁ eτ FY G'
local notation "w★"=> ( Stoop.radius w (Ω^6) )
local notation "ν"=> (pΩ).fidelity
local notation "Y₁"=> (P').p.B
variable (he_C:c_P ≤ 1)(h0:0<e_E)(ht₁:e_E≤1)
include h0 he_C ht₁
open Affinity
local notation "K" => (Ω)
local notation "uA"=> ( Φ (i+1) )
set_option maxHeartbeats 660000
-- expose both.C.Intent.That.Set.Wallet.Eyes all.Imposition.Operation.Size.` next-step Amt.ready proof independent.Spreader.Ø.
structure Combo (Sx:Set Θ) {J:Type}(M': Tint.Incoming (K₁.coarser µ) (Ψ i) (Affinity.Wallet Actors) J R₀) :Prop where
   earning : Earn.Scene.Armada ( tΩ ) w ηL Φout ((pΩ).produce (µ).count*c_P) jJ Pt.count Vh
   school : Earn.Tableau U Actors tΩ
   repair : Affinity.Taut ((K₁.coarser µ).support) Actors U M'.old
   force : Affinity.Crown ((K₁.coarser µ).support) Actors U M'.hard
   local_ : M'.old.Paid w₁ ((Ψ i).p.B) ((Ψ i).p.supportExponent+1+1) (X₁+(3*Ω+Ω^2))
   local_clean : (Deletion.sink Sx M'.old).Paid w₁ ((Ψ i).p.B) ((Ψ i).p.supportExponent+1+1) X₁
   kept : M'.hard.Paid ( Stoop.radius w (K^6)) ((Ψ i).p.B) (Ψ i).p.supportExponent wp
   tuition : M'.old.Paid w ((Ψ i).p.B) ((Ψ i).p.supportExponent+1+1) ((K^rμ)*(X₁+(3*Ω+Ω^2)))
   tuition_clean : (Deletion.sink Sx M'.old).Paid w ((Ψ i).p.B) ((Ψ i).p.supportExponent+1+1) ((K^rμ)*X₁)
   paidForce : M'.hard.Paid w ((Ψ i).p.B) (Ψ i).p.supportExponent ((K^6)^rμ*wp)
   reads : ∀ (x:Affinity.Wallet Actors), Integration.LocalComparison.actualPush Z N n i ((Tint.Patrol.picture M Z₁).density x)=(Tint.Patrol.report tΩ M' G').density x
   Waffle : Earnings.Cashier pΩ G (µ).count (P).p (P').p Ω y₀ G'
   Beamwork : K ≤ budgetR R i
   effort : X₁ ≤ 8*K*(eτ+FY+ ν)
local notation "Φt"=> Combo R hk D Q π Γ Ψ Q0 hℓ Pt V₁ Qa Actors U M Z₁ w ηL jJ Vh Vₜ e_E c_P Sx
lemma joined : ∃ (J:Type), Countable J ∧ ∃ M', Combo R hk D Q π Γ Ψ Q0 hℓ Pt V₁ Qa Actors U M Z₁ w ηL jJ Vh Vₜ e_E c_P Sx M' (J:=J):=by
    let Kx:= Ω; have hb: 4 ≤ K:= MintClock.Page.roofers ..; have he:1 ≤ K:=by linarith; -- test linarith hB unfolding? change in tactic
    let h_t:= Stoop.tighten w _ Yv.positive he hClean
    have hp: 0<( K ):= lt_of_lt_of_le zero_lt_one he; have hv0: Ω⁻¹≤1:=inv_le_one_of_one_le₀ he; have hZ':=Yv.stored he
    obtain ⟨J',hh,Q₁,hA,hX,h_u,h_r,hB,hBc,hτ,hT,hΓ,hΩ,hν⟩:= Oak.companions R g hk D Q π Γ Ψ v C Q0 Y' hℓ hz Pt V₁ V₂ Qa hQ Actors U M Z₁ w₁ ηL jJ Vh Vₜ eτ ξ₁ (mul_le_of_le_one_right (inv_nonneg.mpr hp.le) he_C) hJ hv hZ' hM y hL hY (Stoop.leaves w _ Yv.positive he hP₁) Sx h_t (Lamps.loan_monotone _ (Stoop.tighten w _ Yv.positive he hFull) ((mul_le_of_le_one_left zero_le_one hv0))) (mul_pos (inv_pos.mpr hp) h0) ((mul_le_of_le_one_left h0.le hv0).trans ht₁) -- hv shadow overwritten! rename
    have hl : Q₁.hard.Paid (Stoop.radius w (Ω^6)) (P').p.B (P').p.supportExponent wp:=by
       rw [← (Scene.Armada.wallet (V:=Θ) w K 5 rfl)] -- may fail
       exact hτ
    refine ⟨_,hh,Q₁,?_,hX,h_u,h_r,hB,hBc,hl,Stoop.retake w _ (Yv.quota) Yv.positive he hB,Stoop.retake w _ (Yv.quota) Yv.positive he hBc,Stoop.budget w (Yv.quota) _ Yv.positive (one_le_pow₀ he) hl,hT,hΓ,hΩ,hν⟩
    exact Scene.lit M ( (Xn).ratio ) w ηL uP θρ Yv hΓ.price he_C hΓ.schedule -- defeq.We.
end Buffered
end Oak
end YM.QuadraticLocal.Advent
