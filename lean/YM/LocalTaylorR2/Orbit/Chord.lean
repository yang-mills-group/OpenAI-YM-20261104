import YM.LocalTaylorR2.Orbit.Reeds
import YM.LocalTaylorR2.Orbit.Marks
/-!
 # Paid unweighted error after ticket projection and forced divisor,
   at any fixed **finite total number** of distinct external tokens (has all
   monomials up to it, multiple occurrences of `same visible Source variables` also
   supported by presenting distinct formal source labels, as in Slots grammar).
   This also supplies the results (Budgeted/Strong) to be used before unweighting &
   occupancy/authentication in Library. Strong leaves as before. Price of kernel,
   Part, Eg in actual Tenant contract even when projection into Budget decks.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
open Mallow Blush Lattice Daisy Lotus Daisy.Charity.RG12 UVNext.CouplingReset Extra.Histories Next.Foundations Planned.GuardedAtom
open CalendarStep Recoil _root_.YM.Marker MergeProof Accent Merge Menu Mallow.Many

variable {G:Gauge}{M: Metals G}{D:Rolls M.p}{A:Alloy M D} {g:G.Simple} (R:Factor A) (S:Uses R g)
set_option quotPrecheck false
variable {m N n:ℕ} (hm:m<N) {V ι:Type}[DecidableEq V][Fintype V][Fintype ι]
local notation "T"=> A.B.a.S.side (m+1) n
local notation "Q"=> S.realBeat 0 N n (m+1)
local notation "J"=> (A.B.a.clock.J (m+1))
local notation "j"=> (A.B.a.clock.J m)
local notation "x"=> A.B.a.clock.hatBeta m
local notation "y"=> A.B.a.clock.hatBeta (m+1)
local notation "s₀" => Mallow.station y
local notation "P₀"=> A.B.a.budget (m+1)
local notation "q₀"=> Mallow.probe y
local notation "B'"=> A.B.a.budget m
local notation "H"=> Marker.beam R S hm (n:=n)
local notation "U₀"=> (H).result Orchard.beam0
local notation "Φ"=> Orchard.beam0
local notation "i₀"=> houseS H Φ
local notation "δ₀"=> A.B.a.clock.forcedAllowance m
local notation "p'"=> A.B.a.params m
variable {C:Family G}{Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g (modes Δ))
section reeds
variable (o:V→Site (A.B.a.S.side (m+1) n)) {B:Marker.Census V} (s:ι→Hat B (S.realBeat 0 N n (m+1)))
    (K p C₀:ℕ)
local notation "l"=> (escalate K C₀ p)
local notation "o₀"=> (A.B.a.clock.op m n).ratio.parent ∘ o
local notation "r"=> (fun _ : V=> (y^(K+2))⁻¹)
local notation "uS"=> heap s
local notation "t"=> (l:ℝ) -- don't use numer
local notation "f₀"=> fun i=> (heap s i).M
local notation "fS"=> fun i=>Menu.sumFee (heap s i) r
local notation "vS"=> fun i=>Menu.sing (heap s i) r
local notation "dK"=>pupilK H Orchard.beam0 f₀ fS
local notation "p1"=> Photo.Fleece dK B vS
local notation "a₀"=> (Orbit.sketch i₀ Chi.canonical f₀ fS B vS l true)
local notation "w₀"=> Orbit.fullS i₀ Chi.canonical f₀ fS B vS l
local notation "e₀"=> (Orbit.sketch i₀ Chi.canonical f₀ fS B vS l false)
local notation "l'"=> (y^((K+2)*C₀))
local notation "f"=> Mallow.straw (R.shape.μ J j) (D.L J) G (A.B.a.clock.hatBeta m) -- precision
local notation "d0"=> A.B.a.clock.op m n
structure Rich (ε v:ℝ) : Prop where
   strong : StrongR2 H Φ l B (heap s) o r (y^requested (l+1) ε)
   orbit : Menu.Offer o (heap s) r (Q).p.B ((Q).p.supportExponent-4) (Mallow.station y)
   scope : shop i₀ B (1:V→ℝ) o₀ (U₀).p (e₀) v∧ (inquiries B (1:V→ℝ) o₀ U₀ p1 (l'*f)∧ (Real.sqrt δ₀)⁻¹*(l'*f) ≤ v) ∧
      Menu.Expense uS r d0 = Orbit.coflow s ∧ (∀ U,(coflow s U).part B.quiet=(Q).eval U) ∧ (d0).push (Q).beta (coflow s)=refer i₀ B U₀ w₀ p1 ∧
      (∀ U',(refer i₀ B U₀ w₀ p1 U').part B.quiet=(U₀).eval U')
variable (he:(A.B.a.budget m).supportExponent=100)(hev:(A.B.a.budget (m+1)).supportExponent=100)(hB:Mallow.RG12.Earned (orbitD G) R.shape A.delay)(hS:Mallow.Arrives R.shape A.delay)(hv: Fintype.card V ≤ C₀)
include hv hS hB hm he hev
set_option maxHeartbeats 550000 in
lemma richer (hl:escalate K C₀ p≤J) (hΩ: Extra.Multi.Occupancy o₀ (J+1)) (ht:Offer o s (1:V→ℝ) (Q).p.B ((Q).p.supportExponent-4) (y^K)) (ε v:ℝ) (hε:loss J ≤ ε)(hε':0≤ε)(hx:y^(requested (p+1) ε) ≤ v): Rich R S hm o s K p C₀ ε v:=by
    let Rπ:= (H); let V':= Rπ.result Φ; let Q':=(Q); let J':= uS; let M₀:= r; let E:=d0; let ε':= y^(requested (l+1) ε); let v':=y^(requested (p+1) ε)
    let P:=A.B.a; have htS:= (Mallow.minted_same R.shape hB).word J x (A.B.valid.pays m) j (step_paid A.B.a m)
    have hX':Q'.p=(P₀):= (Rπ.knows _ (Φ).2).1.point
    have hN: (Q').p.supportExponent≥100:=by rw [hX',hev]
    have hY:1≤ y:= (A.B.a.fits.delayed _).le
    have hw:∀ i:V,0< M₀ i:= fun _=> inv_pos.mpr (pow_pos (zero_lt_one.trans_le hY) _) -- check
    have hsQ := Orbit.authorized R S hm hw o s hev htS (goDown s o K (y) hY ht)
    have hr:= Many.sailR2 g hm H Φ hN (show 100 ≤ V'.p.supportExponent from he.ge) hS hB l B (heap s) o M₀ hw hΩ hsQ hl ε' (Real.rpow_le_rpow_of_exponent_le hY (by unfold Tail.requested; linarith only [hε]))
    have hy₀:= hr.carry.stamp; have ht:=hy₀.hard.1; have hU := Orbit.duty (B:=B) (K+2) y hY C₀ hv
    have hh: 0 ≤ l':= by positivity
    obtain ⟨hℓ,hℓ'⟩:= Orbit.powers K C₀ p hY hε'
    obtain ⟨hP,hQ⟩:= (Rπ.knows _ (Φ).2)
    have h:= hr.canopy
    have hxU:V'.Lawful (p').width (p').paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) δ₀:= ((Rπ.moves g hm).2 _ (Φ).property).1.bundle.valid
    obtain ⟨hz,hF⟩:= exact_heap s hP.valid E hw -- arg R collides; fix
    have hV : E.push (Q).beta (coflow s)= refer i₀ B U₀ w₀ p1:=hz ▸ (hy₀.physical.1 : E.push (Q).beta (Menu.Expense uS r E)=_) -- coercions; might rw problem
    refine ⟨hr,hsQ, ⟨Orbit.opened i₀ B (1:V→ℝ) o₀ (Orbit.billUpS hh hU hy₀.pass.2) (hℓ.trans_le hx),⟨⟨ht.1,Orbit.billUpT _ hh hU ht.2⟩,?_⟩,hz,fun i=> (hF i).2,hV,?_⟩⟩
    · calc _ = l'*((Real.sqrt δ₀)⁻¹*f) := mul_left_comm .. -- direction
           _ ≤ l'*y^(-(l+1:ℝ)) := mul_le_mul_of_nonneg_left hr.divisor hh
           _ ≤ _:= hℓ'.trans hx
    intro U
    let F₀:=rigInk H Φ B uS M₀; let Y₀:=rSeat H Φ B uS M₀
    rw [←hV, ← hz, show E.push (Q).beta (Expense uS M₀ E)=_ from (h.2.2.2.2.1 : _=Accent.play U₀ B Y₀ (fun U=>∑ i,F₀ i U))];
    apply bronze (U₀) B _ _ _ hxU.labels (fun i=> h.2.2.2.2.2.1 i U); rw [Poly.part_sum]; exact sum_eq_zero (fun i _=> (h.2.1 i).sil U)
end reeds
end YM.LocalTaylorR2.Orbit
