import YM.LocalTaylorR2.Orbit.Trunk
/-!
 # Fidelity input with MARKERS. Address-by-address not hidden K.profile choices.
 `coflow` is literally the product density coupling in the nilpotent ring
 -- wherever marks choose the *same* E role, their symbols with actual inputs
 are ADDED in log, providing all powers in the projected degrees. Wherever a mark
 chooses K, it updates that eligible occurrence (several symbols there permitted; gas only takes
 that one *address* once). See Masks & Option reservations through StrongR2.

 Even though marks carrying blank E's supplied by Leaf use masked-profiles rather than unmasked
 Regular themselves, pure pass evaluation sees exact true fields selected. `h.project / h.clothes`
 below only required to instance this source bill for ALL those weights at once. Prices
 after converting to `heap` slot carrying simultaneous mark), fit in Arc. -/
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

variable {G:Gauge}
section insist
variable {n:Side} {J V:Type} [DecidableEq V] {B:_root_.YM.Marker.Census V} {P:Rep G n} {σ C a c d e t x:ℝ}
variable [Fintype J] [Fintype V]
variable (s: J→Menu.Hat B P)(r:V→ℝ)
-- same-address Binder and PriceB takes joint perimeter. Teach actual Ω
abbrev coflow (U:Config G n): Poly B:= (Real.exp (P.exponent U):ℂ) • (Poly.pass (Menu.roll s U)*∑' p:Finset ℕ, Merge.Photo.fronts P.activities (fun i=> Menu.Kunt s i U) U P.p p)
variable {r} (h:P.Lawful σ C a c d)
include h
lemma exact_heap {L:Lattice.Side} (S:StepData L n) (he:∀ i,0<r i) : Menu.Expense (Menu.heap s) r S= coflow s ∧ ∀ U:Config G n, Summable (Merge.Photo.fronts P.activities (fun i=>Menu.Kunt s i U) U P.p) ∧ (coflow s U).part B.quiet=P.eval U:=by
  let V U:= Accent.play P B (fun i U=>bar P.activities B U i+board s i U) (roll s) U
  have ht U: coflow s U= V U:= by
    unfold V play; rw [show (fun p=> bar P.activities B U p+Menu.board s p U)=_ from (Menu.win s h U).symm, Accent.rock_out P.activities P.p U _ he (Menu.fence s h he U).1]; rfl
  constructor
  · funext U; unfold Menu.Expense; rw [Menu.passIn (Menu.heap s) S h he, Menu.golden, Menu.banded,ht]; rfl
  intro U; refine ⟨Menu.sectioned s h U,?_⟩; rw [ht]; apply Accent.bronze (P) B _ _ _ h.labels ?_ ?_
  · intro i; let K v:= Menu.rush s (Lotus.Wing.gasKey v) U; change ((_ + Menu.board s i U).part B.quiet)=_; rw [Poly.part_plus]
    unfold Accent.bar Menu.board; change (_ + (∑' v:{i'// barcode P.activities i'=i}, K v.val).part _) = _
    rw [Poly.share (f:=fun j:{j' // barcode P.activities j'=i}=> K j.val) ((Menu.chair s U).comp_injective (i:=Subtype.val (p:=fun v=>barcode P.activities v=i)) Subtype.val_injective) B.quiet]; unfold K; simp only [Menu.still, tsum_zero, add_zero]; simp [Poly.bead]
  unfold roll; rw [Poly.part_sum]; simp [Menu.still]

-- scale conversion from a polynomial-weight aperture. price includes exp(H), ANY orientation size. Require individual Marker symbol dimension not neglected -- after p budget choose.
omit h
local notation "q"=> x^(t:ℝ)
omit [Fintype V] in
lemma discount {w:ℝ} (hw:0<w) (he:w≤1) (p:Hat B P) : fare p (fun _=>w) ≤ w* (fare p 1):=by
    obtain ⟨i,hi⟩:=p.shiny; let F:= p.s.val
    have hx: Poly.toll (fun _=>w) p.s≤ w:=by
       rw [Poly.toll,← mul_prod_erase _ _ hi]; exact mul_le_of_le_one_right hw.le (Finset.prod_le_one (fun _ _=>hw.le) (fun _ _=> he))
    have h: Poly.toll (1: V→ℝ) p.s=1:=by unfold Poly.toll; simp
    unfold Menu.fare sumFee; rw [h,one_mul,← mul_assoc]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) p.M.profit
-- any Marker demand measured in Hat price . *normalization point. arity weight marker issue with x^(τ). Need Seeds actual ξ. Choose enough after (~#mark). `ρ=1` floor then.
variable (o:V→Site n)
omit [Fintype J] [Fintype V] in
lemma goDown (v:ℕ)(y:ℝ) (hy:1≤y) (he: Menu.Offer o s 1 P.p.B e (y^v)): Offer o s (fun _=> (y^(v+2))⁻¹) P.p.B e (Mallow.probe y) := by
    let f:ℝ:=(y^(v+2))⁻¹; have ht:0<y:= zero_lt_one.trans_le hy; have hf : 0<f:=by unfold f; positivity
    have hp:f≤1:= (inv_le_one₀ (by positivity)).2 (one_le_pow₀ hy)
    have hz: f*y^v=Mallow.probe y:=by unfold Mallow.probe f; rw [Real.rpow_neg ht.le, Real.rpow_two,pow_add]; field_simp -- edit
    rw [← hz]; refine ⟨he.sites,fun i=> budget_mono (budget_scale hf.le (he.budget i)) ?_ ?_⟩
    · intro j; split
      · exact mul_nonneg (Crew (p:=s j) (fun _=>f) (fun _=> hf)) (Real.exp_nonneg _)
      exact le_rfl
    intro j; dsimp only; split_ifs
    next h => exact (mul_le_mul_of_nonneg_right (discount hf hp (s j)) (Real.exp_nonneg _)).trans_eq (mul_assoc ..)
    rw [mul_zero]

end insist
-- stage conversion to heap bill (part of forging offers)
variable {M: Metals G}{D:Rolls M.p}{A:Alloy M D} {g:G.Simple} (R:Factor A) (S:Uses R g)
     {m N n:ℕ} (hm:m<N) {V ι:Type}[DecidableEq V][Fintype V][Fintype ι] {r:V→ℝ}(hr:∀ i,0< r i)
local notation "T"=> A.B.a.S.side (m+1) n
set_option quotPrecheck false
local notation "Q"=> S.realBeat 0 N n (m+1)
local notation "J"=> (A.B.a.clock.J (m+1))
local notation "j"=> (A.B.a.clock.J m)
local notation "x"=> A.B.a.clock.hatBeta m
local notation "y"=> A.B.a.clock.hatBeta (m+1)
local notation "s₀" => Mallow.station y
local notation "P₀"=> A.B.a.budget (m+1)
local notation "q₀"=> Mallow.probe y
variable (o:V→Site (A.B.a.S.side (m+1) n)) {B:Marker.Census V} (s:ι→Hat B (S.realBeat 0 N n (m+1)))
    (hX: (A.B.a.budget (m+1)).supportExponent=100)
    (hT: Mallow.Tariff (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.J (m+1)+1) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m))
    (he: Offer o s r (S.realBeat 0 N n (m+1)).p.B ((S.realBeat 0 N n (m+1)).p.supportExponent-4) (Mallow.probe (A.B.a.clock.hatBeta (m+1))))
local notation "e₀"=> ((P₀).supportExponent-4)
include hm hr hX hT he
omit [Fintype V] in
lemma authorized : Menu.Offer o (Menu.heap s) r (Q).p.B ((Q).p.supportExponent-4) s₀:=by
  have hh: (Q).p=P₀:= ((S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hm).1.point
  let a:= Mallow.radiusTab ((P₀).B) (J+1) q₀; have hp : y=Pressure.betaF G x (D.L J):= beta_eq A.B.valid m
  have hv : a+Real.exp a*a ≤ s₀:=by unfold a; rw [show (P₀).B= Pressure.radiusB y from rfl,hp]; exact hT.buy
  have hq:0≤ q₀:=by unfold Mallow.probe; exact Real.rpow_nonneg (zero_le_one.trans (A.B.a.fits.delayed _).le) _
  have hz:q₀≤ a:=by
    unfold a radiusTab; apply le_trans (b:=(4:ℝ)*q₀); · linarith only [hq]
    exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by positivity) (show 0≤ Extra.Multi.siteFactor (P₀).B from (by unfold Extra.Multi.siteFactor; positivity))) hq)
  have hf:(Q).p.supportExponent-4 ≥ 0:=by rw [hh,hX]; norm_num
  apply Menu.Offer.fatten (Menu.counts s r o ((Q).p.B) hr he hf)
  apply le_trans _ hv; exact add_le_add hz (mul_le_mul (Real.exp_monotone hz) hz hq (Real.exp_nonneg _))
end YM.LocalTaylorR2.Orbit
