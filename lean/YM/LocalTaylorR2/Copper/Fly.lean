import YM.LocalTaylorR2.Copper.Bistro
/-! Adapt Chord. Uses ALSO the scale stability of Regular main with inherited E propagated at least p+6 further than requested.
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
open Grafting
variable (ψ: Reel.Scroll G (A.B.a.S.side (m+1) n))
variable (Ξ:King.Engine G)
local notation "E!"=> Orbit.errT i₀ Chi.canonical f₀ fS B vS l ψ Ξ
-- Rich transferred without re-weighting marks in main. Cost retained.S stronger even after rewriting vacuum μ (using same calibration at this step).
structure Voyager (ε v b :ℝ) : Prop where
   rich : Rich R S hm o s K p C₀ ε v
   usedE : Cinema H Φ l B (heap s) o r ψ Ξ (y^requested (l+1) ε) (4*(y^requested (l+1) ε)) b
   grace : shop i₀ B (1:V→ℝ) o₀ (U₀).p E! (6*v) ∧ Towed (1:V→ℝ) id (visitor i₀ B U₀ E!) (U₀).p.B (Quotes.preExponent (U₀).p) (6*v)
local notation "Φ₁"=> Reel.upfront y (troop l) -- eps argument later
variable (hP: Mallow.RG12.Earned (Mallow.roadD G) R.shape A.delay) (hl:escalate K C₀ p ≤ A.B.a.clock.J (m+1))
     (hc:Fintype.card V ≤ C₀) (ε v:ℝ)(hε:0<ε)(hR:Rich R S hm o s K p C₀ ε v)
include hP hl hc ε v hε hR
lemma surpass (hr:CalendarStep.loss (A.B.a.clock.J (m+1)) ≤ ε) (hg:Mallow.RG12.Earned (sunsetD G Ξ) R.shape A.delay)(hx:y^requested (p+1) ε ≤ v)(he:Reel.Affords Q A.B.a (m+1) ψ (Reel.upfront y (troop l) ε)):
      Voyager R S hm o s K p C₀ ψ Ξ ε v (2*y^(21/10:ℝ)*(Φ₁ ε)):=by
   have hq:1≤y:= (A.B.a.fits.delayed _).le; let W:= (r); have hr1 : ∀ i:V,0 < W i:= fun i=> inv_pos.mpr (pow_pos (zero_lt_one.trans_le hq) _)
   let v':= y^requested (l+1) ε; let Y:= H; let U':=U₀
   have h:= tour hm Y Φ l B (heap s) o r ψ he hP Ξ hg hR.strong hr1 hR.orbit hl (show (2*y^(3:ℕ))*(Φ₁ ε) ≤ 4*v' from (Grafting.charge l (y) ε (zero_lt_one.trans_le hq)).le) (show (y)^requested (l+1) (CalendarStep.loss J) ≤ v' from Real.rpow_le_rpow_of_exponent_le hq (by unfold requested; linarith only [hr]))
   have hd : 0≤ l':=by positivity
   have ht:= billUpS («H»:= i₀) hd (duty (K+2) (y) hq C₀ hc) h.temple.pass.1
   have hf: (l':ℝ)*(v'+(4*v'+v'))≤6*v:= calc
     _ = 6*((l':ℝ)*v'):= by ring
     _ = _:= congr_arg (6*·) ((Orbit.powers K C₀ p hq hε.le).1) -- add Y bound annotation
     _ ≤ _ := mul_le_mul_of_nonneg_left hx (by norm_num)
   have hK:= opened _ _ _ _ ht hf
   exact ⟨hR,h,hK,(viscera i₀ B (1:V→ℝ) (fun _=>zero_lt_one) o₀ U₀ hK).1⟩
end reeds
end YM.LocalTaylorR2.Orbit
