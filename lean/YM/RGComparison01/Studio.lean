import YM.RGComparison01.Cuprite.Parade

/-!
# Joined chronology of all finite orders.

 Choose post tables; on THIS same Factor, any order in steps paid with
 maturing Stage. Layout before βEntry allows after-block finite-stencil
 and monitor costs. Frames co-selected among all strengthening. Need
 prediction supplying the chosen Buyer's hypothesis; not saying all analytic
 profiles fit any Buyer budget.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage AuxBeam AuxSpell AuxJets AuxStage
open Push.AbsoluteSums.Animals Slide Tensor WilsonStartup Bouquet Push.PriceCompiler
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves
open RG.Supply Shoot Input Org Ovens Progress.DirectedRecipe Next.Scheduling Further.PhysicalPeriodLimitF933
open Vision
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {X : Metals G} {D : Rolls X.p} {J : Targets X.p X.K}
  {E : Expenses J} {W : Return.Wages} {v : ℕ→ℝ}
    (R : PhysicalNext.Repeat.Register D E W v)

/-- public post demand calibrated by requester. lookahead in prior grants.
 d,ν only summoned after these and other choices. Does not yet allow Plateau choice to see the actual hitting Alter delays. -/
structure Layout (G:Gauge) (L : Side) where
  stencil : ℕ
  inRank : ℕ
  outRank : ℕ
  counts : Kraal.Buyer G L
-- requester may need upper grants post-L on projection exponents. Permit projections in D,C
abbrev Sponsor (G:Gauge) := (X : Metals G) → (D:Rolls X.p) → Targets X.p X.K → ∀ _i j _k : ℕ, Layout G (D.L j)

variable (P : Sponsor G) (i j k:ℕ)
namespace Studio
variable (h : 4≤j)
abbrev stage (p:ℕ) := X.p.profile p
local notation "D₀" => (D.L j)
local notation "B₀" => (Mural.sheet X.p D h)
local notation "Y" => (P X D J i j k)
local notation "X₁" => (X.p.profile j)
local notation "X₂" => (X.p.profile i)
set_option quotPrecheck false
local notation "Y'" => (X.p.profile i).order
local notation "H" => (J j i)
abbrev nBudget (p q j n : ℕ) := n+2+j+n+(0+p*n)+q+1
local notation "q" => (P X D J i j k).inRank
local notation "u" => (P X D J i j k).outRank
local notation "n₀" => nBudget (q) (u) (X.p.profile i).order k
local notation "f₀" => (P X D J i j k).stencil
local notation "A₀" => escrow (H).halo (f₀) (High.countOrder (k+1))

-- grants exposed even before path used. width/scales
structure Staff (D' : ℝ) (r s t : ℝ→ℝ) (hh:Geo G D₀ r)
    (A : Before G (X.p.profile j).width (X.p.profile j).paths (B₀).J X.p.kernel (nBudget (P X D J i j k).inRank (P X D J i j k).outRank (X.p.profile i).order k +3))
    (E₀ : BareRates.pre G (X.p.profile i).width (X.p.profile i).paths n₀)
    (η : ℝ) (x : ℝ) : Prop where
  wave : Real.exp 1≤x
  crossing : let ρ:= (Y).counts A₀ D' r hh; Kraal.Launch (d:=fun t=> Trio.paySide G D₀ A₀ t) (σ':= (X.p.profile i).width) (C':=(X.p.profile i).paths)
    H (R.o j i) (Mural.sheet X.p D h) A (X₁).clip (X₂).clip (R.μ j i) ρ.letters q k Y' r ρ.f ρ.const D' s t x
  pays : let g:= (Y).counts A₀ D' r hh
         ∀ B:BudgetPoint,B.B=radiusB x→ B.supportExponent=(X.p.profile i).supportExponent → Marlin.tithe (2*Trio.base A₀ (radiusB x)) (Vision.guessT G D₀ (H).halo (f₀) (High.countOrder (k+1)) X₂ g.v x) B (Trio.coverTicket A₀) ≤ Pressure.betaF G x D₀ ^ (-(1/8):ℝ)
  periods (β:ℝ) : Pressure.betaF G x D₀ /2 ≤ β∧ β ≤ 2*(Pressure.betaF G x D₀) →
      let p := r x * gStep β
      let c:= (Y).counts A₀ D' r hh
      0 < β ∧ 1 < r x ∧ furl G D₀ x < p ∧ 0 < furl G D₀ x ∧ p ≤ 1 ∧ Sluice.Shore G D₀ Y' x p ∧ Sluice.Health G D₀ (Trio.base A₀ (radiusB x)) x p ∧
        Loads.salary A₀ k u q D₀ X₂ c E₀ r t |Pane.cloak D j| x * gStep β^(k+1) ≤ gStep β^((k+1:ℕ)-η:ℝ)

structure Cloud (G:Gauge)(L:Side)(S:Stage) where
  frame : Ward.Duplex G (S.order+1)
  r : ℝ→ℝ
  larger : Geo G L r
  t : ℝ→ℝ
  s : ℝ→ℝ
  gets : Geo G L t
  keeps : Geo G L s
structure Chair (D' : ℝ) (r t : ℝ→ℝ) (hh:Geo G D₀ r)
    (A : Before G (X.p.profile j).width (X.p.profile j).paths (B₀).J X.p.kernel (nBudget (P X D J i j k).inRank (P X D J i j k).outRank (X.p.profile i).order k +3))
    (E₀ : BareRates.pre G (X.p.profile i).width (X.p.profile i).paths n₀)
    (Z:Cloud G D₀ X₂) (x:ℝ) : Prop where
  direct l (β:ℝ) : Pressure.betaF G x D₀ /2 ≤ β ∧ β ≤ 2*(Pressure.betaF G x D₀) → 1 < Z.r x ∧ Z.r x*gStep β ≤ 1 ∧ Z.frame.Blurb (Trio.fence A₀ (radiusB x) l) (r x*gStep β) (Z.r x*gStep β) (furl G D₀ x)

  uplink : let ρ:= (Y).counts A₀ D' Z.r Z.larger; Kraal.Launch (d:=fun t=> Trio.paySide G D₀ A₀ t) (σ':= (X.p.profile i).width) (C':=(X.p.profile i).paths)
    H (R.o j i) (Mural.sheet X.p D h) A (X₁).clip (X₂).clip (R.μ j i) ρ.letters q k Y' Z.r ρ.f ρ.const D' Z.s Z.t x
  scales (i':Stars): let ρ:= (Y).counts A₀ D' r hh
                     2*Z.frame.conjCost (Y') (Trio.fence A₀ (radiusB x) i') * Cuprite.bill A₀ n₀ k D₀ (X₂) |Pane.cloak D j| Z.r E₀ Z.t x ≤ Loads.rateP A₀ k (u) (q) D₀ (X₂) ρ E₀ r t |Pane.cloak D j| x
  heads (β:ℝ) (hx:0<β) (hp:Pressure.betaF G x D₀/2 ≤ β): Cuprite.headBudget A₀ n₀ k (q) D₀ (X₂) |Pane.cloak D j| Z.frame E₀ Z.r Z.t x*gStep β^3≤ gStep β^((5/2):ℝ)
structure Workshops (η:ℝ) (V:ℝ) where
  uS : ℝ
  grows : 0<uS -- auxiliary cutoff
  r : ℝ→ℝ
  waits : Geo G D₀ r
  before : Before G (X.p.profile j).width (X.p.profile j).paths (B₀).J X.p.kernel (nBudget (P X D J i j k).inRank (P X D J i j k).outRank (X.p.profile i).order k +3)
  E₀ : BareRates.pre G (X.p.profile i).width (X.p.profile i).paths (nBudget (P X D J i j k).inRank (P X D J i j k).outRank (X.p.profile i).order k)
  aP : ℝ→ℝ
  enter : Geo G D₀ aP
  tP : ℝ→ℝ
  fee : Geo G D₀ tP
  Staffer (x:ℝ) (hx:V ≤ x) : Staff R P i j k h uS r aP tP waits before E₀ η x
  warp : Cloud G D₀ (X₂)
  lifts (x:ℝ) (hx:V ≤ x) : Chair R P i j k h uS r tP waits before E₀ warp x

lemma purchase (V η : ℝ) (hp: 0 < η) (hi:StepStages j i) (hk:1≤ k) :
    ∃ B : ℝ,V ≤ B ∧ ∀ U : ℝ,B ≤ U → Nonempty (Workshops R P i j k h η U) := by
  let L:=D₀; let X' := Mural.sheet X.p D h; let Y₁:=X₁; let Y₂:= X₂; let n:=n₀; let b:= A₀
  obtain ⟨r,hr,hR⟩:= Sluice.fixed G D₀ Y₂.order (fun x=>Trio.base A₀ (radiusB x)) (Geo.basic (Trio.rows G L b|>.2.2.1))
  have hQ: 2 ≤ n := by unfold n nBudget; omega
  obtain ⟨P'⟩:= Uniform.pre_order G Y₁.width Y₁.paths X'.J X.p.kernel (n:=n+3) (by omega)
  let V₁:= Classical.choice (BareRates.offered G Y₂.width Y₂.paths (n+3)); let E₀:= Classical.choice (BareRates.offered G Y₂.width Y₂.paths n)
  have hL:=R.consumes j i hi
  have hv:= (Trio.circles G L b)
  obtain ⟨z,hz,hS⟩:= Kraal.laces (H) (R.o j i) X' P' Y₁.clip Y₂.clip (show Bolt G X'.L (fun x=>Trio.paySide G L b x) from hv) (Classical.choice (Planned.JetPort.purchase (H).table (H).table_exists _)) V₁ hL.2.1 (show _ from (by unfold nBudget; omega : k+(0+q*k)< n₀)) (by unfold nBudget; omega : k+2<n₀) (show Y'<n₀ from (by unfold nBudget; omega)) hk
  let c:= (Y).counts A₀ z r hr
  obtain ⟨aP,Tp,ha,hT,H₀⟩:= hS r c.f hr c.ease c.const c.letters
  obtain ⟨F⟩:= Ward.polarized G (Y₂.order+1)
  obtain ⟨r',hr',hh⟩:= Cuprite.prior F b r hr
  let c':= (Y).counts A₀ z r' hr'
  obtain ⟨sP,t₀,hQ,hF,hP⟩:= hS r' c'.f hr' c'.ease c'.const c'.letters
  obtain ⟨tP,ht,hX,hY⟩:= Cuprite.remit b n (q) k L Y₂ |Pane.cloak D j| r' E₀ t₀ F hr' hF Tp hT c r (u) hr
  let Z': Cloud G L Y₂:= ⟨F,r',hr',t₀,sP,hF,hQ⟩
  have heV:= (Cuprite.charged b n (q) k L _ |Pane.cloak D j| r' E₀ t₀ F hr' hF).loss (by norm_num : (0:ℝ)<1/2) 3
  simp only [Nat.cast_ofNat,show 3-(1/2)= (5/2:ℝ) by norm_num] at heV -- implicit conversion
  have hZZ : ∀ᶠ t in atTop, Chair R P i j k h z r tP hr P' E₀ Z' t:=by
     filter_upwards [hh,hP,heV,hR] with x hx hP hg hR
     refine ⟨fun i β h=> hx i β h.1 (hR β h |>.1) (hR β h |>.2.1) (hR β h |>.2.2.1),hP,fun i=> hY i x,fun β h hv=>?_⟩
     exact (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (Fare.gS β h|>.1.le) _)).trans (hg β h hv)
  let t:= Loads.salary A₀ k (u) (q) L Y₂ c E₀ r tP |Pane.cloak D j|
  have he : Geo G L t:= Loads.wages _ _ _ _ _ _ c E₀ r tP _ hr ht
  have hp : ∀ᶠ x:ℝ in atTop, Staff R P i j k h z r aP tP hr P' E₀ η x := by
    filter_upwards [eventually_ge_atTop (Real.exp 1),H₀,Vision.pundit G L (H).halo (f₀) (High.countOrder (k+1)) X₂ c.v c.keeps,hR,Geo.loss he hp (k+1)] with x hx h H₁ hv ht
    refine ⟨hx,Cuprite.liftH (hX x) h,H₁,fun β hy=>?_⟩
    obtain ⟨hβ,hv₀,hv',hd,hh,hS,hX⟩:=hv β hy
    exact ⟨hβ,hv₀,hv',hd,hh,hS,hX, (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (Fare.gS β hβ|>.1.le) _)).trans (ht β hβ hy.1)⟩
  obtain ⟨U,hU⟩:= eventually_atTop.mp (hp.and hZZ)
  refine ⟨max U V, le_max_right .., fun W h=> ⟨⟨z,hz,r, hr,P',E₀,aP,ha,tP,ht,fun x hx=> (hU _ ((le_max_left ..).trans (h.trans hx))).1,Z',fun x hx=> (hU _ ((le_max_left ..).trans (h.trans hx))).2⟩⟩⟩
end Studio
end YM.RGComparison01
