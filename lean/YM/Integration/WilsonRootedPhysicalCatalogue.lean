import YM.Integration.WilsonRootedPhysicalPathCover

/-! The actual strong regular cover quote on all retained original physical leaf addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalCatalogue
open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonRootedPhysicalPathCover
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {m N per : ℕ} (S : Station R N per m)
local notation "H" => S.guide
local notation "B" => R.alloy.B.a.budget m
local notation "X" => ledger R.kit H
local notation "α" => R.alloy.B.kin.alpha N m
local notation "J" => R.alloy.B.a.clock.J
local notation "θ" => R.alloy.B.a.clock.hatBeta
local notation "K" => R.alloy.B.a.params m
local notation "U" => R.family.path.rep N per (m+1)
local notation "a₀" => R.kit.expense (J (m+1)) (J m)
local notation "cut" => lit R.kit H H S.identity
local notation "readAt" => Height.lower H S.identity Chi.canonical

/-- Kept before field integration and the orbit reconstruction. -/
def gross (cap period level : ℕ) :=
  let a:=R.alloy.B.a
  let k:=a.params level
  let b:=a.budget level
  let wage:=R.kit.expense (a.clock.J (level+1)) (a.clock.J level)
  (a.clock.hatBeta (level+1))^wage.wanting +
    octaveNeed G (regularPoint b) k.clip (2*k.width/3) k.paths (a.clock.loopCap level)
      (R.family.path.rep cap period (level+1)).beta (R.alloy.B.kin.alpha cap level)

theorem original (salary : WilsonOriginalHighSelection.Salary G R.kit) (hm : m<N) (r : ℕ) :
    ∃ f : Magazine H→ℝ, Footprint.Anchored (fun i=>(contents H B i).site) f
      (fun i=>coverNumber (B).B (contents H B i).support) (preExponent B+1) (gross R N per m) ∧
      ∀i,(B).Regular (contents H B i).support (readAt (cut r) α i) ∧
        (B).supBounds (contents H B i).site (contents H B i).support (readAt (cut r) α i) (f i) := by
  let a:=R.alloy.B.a
  let c:=J m
  let j:=J (m+1)
  let x:=θ m
  let T:=ships R.alloy.B N m per
  let p:=regularPoint B
  have pay:=R.alloy.B.valid.pays m
  have step : StepStages j c:=step_paid R.alloy.B.a m
  have hr : a.params m=R.metals.p.profile c:=params_eq R.alloy.B.valid m
  have room : preExponent B/(B).B≤(K).width/2 := by
    change ((a.params m).supportExponent+3)/radiusB x≤_
    rw [hr]
    exact R.kit.pledging.range j x pay c step
  have decent:=CensusStep.decent R.kit (N:=N) hm
  have decent' : Decent (K).clip p:=⟨decent.direct,decent.radius,decent.cut⟩
  obtain ⟨bare,estimate,witness⟩:=WilsonRootedPhysicalPathCover.original (n:=R.family.side m per) B T.down (U).beta α
    (R.alloy.B.support.cap N m hm.le) decent' room
  obtain ⟨old,record,price⟩:=WilsonRootedPhysicalCashCover.original R S salary hm r
  have heights:=R.kit.pledging.jewels j x pay c step
  obtain ⟨Y',d',v,t',Av,b',r',B',q',i',z,⟨cap,g⟩,admit,amount⟩:=
    heights.2 _ _ _ T (H).laws.data.funds (protocol R.alloy.B hm R.kit.pledging.conducts.full) _ H
  have hj : (B).order=(R.metals.p.profile c).order:=congr_arg RG.Stage.order hr
  have hp : (B).power=(R.metals.p.profile c).power:=congr_arg RG.Stage.power hr
  have regular (i : (H).fragrances) : (B).Regular (dashboard H i).support (readAt (cut r) α (.inl i)) := by
    have keep:= (VacuumListing.pocket_dash H B Chi.canonical S.identity cap rfl hj.le hp.le i).1
    by_cases h : cut r i
    · simp only [Height.lower,Height.chosen,Sum.elim_inl,h,↓reduceIte]
      exact CouplingShape.reg_const _ 
    · simpa only [Height.lower,Height.chosen,Sum.elim_inl,if_neg h,Song.opus] using keep
  refine ⟨Sum.elim old bare,?_,?_⟩
  · intro y
    have same : preExponent (regularPoint B) = preExponent B+1:=by unfold regularPoint preExponent;dsimp only;ring
    have e:=estimate y
    change SumBudget (fun i=>if (strings T.down B i).site=y then bare i*Real.exp
      ((preExponent (regularPoint B))*coverNumber (B).B (strings T.down B i).support) else 0) _ at e
    rw [same] at e
    exact Cost.sum (price y) e
  · rintro (i|i)
    · exact ⟨regular i,record i⟩
    · simp only [Height.lower,Height.chosen,Sum.elim_inr,↓reduceIte,Song.opus]
      have h:=(witness i).1
      exact ⟨⟨h.sites,h.borel,h.symmetry,h.smooth,h.hasDerivs⟩,(witness i).2⟩

/-- The physical masked and smooth orbit listing buys the same extra unit after all original spins. -/
theorem orbit (salary : WilsonOriginalHighSelection.Salary G R.kit) (hm : m<N) (r : ℕ) :
    ∃ f : ℕ→ℝ,
      (∀i,(B).supBounds ((X).reg i).site ((X).reg i).support ((kept R.kit H H S.identity r).logRead i) (f i)) ∧
      Footprint.Anchored (fun i=>((X).reg i).site) f (fun i=>coverNumber (B).B ((X).reg i).support)
        (preExponent B+1) (turnFee (regularPoint B)*gross R N per m) := by
  obtain ⟨f,fee,rows⟩:=original R S salary hm r
  let p:=regularPoint B
  have same : preExponent p=preExponent B+1:=by unfold p regularPoint preExponent;dsimp only;ring
  have credit : Quotes.early p (contents H B) f (gross R N per m):=by
    unfold Quotes.early
    rw [same]
    exact fee
  have reg (i) : p.Regular (contents H B i).support (readAt (cut r) α i):=by
    have h:=(rows i).1
    exact ⟨h.sites,h.borel,h.symmetry,h.smooth,h.hasDerivs⟩
  have priced (i) : p.supBounds (contents H B i).site (contents H B i).support (readAt (cut r) α i) (f i):=(rows i).2
  obtain ⟨h,q⟩:=Song.spiral (contents H B) (readAt (cut r) α) f reg priced credit
  refine ⟨_,fun i=>(h (pennant H i)).2,fun y=>?_⟩
  have read:=Cost.equiv (pennant H) (q y)
  change SumBudget (fun i=>if ((X).reg i).site=y then _*Real.exp (preExponent p*
    coverNumber (B).B ((X).reg i).support) else 0) _ at read
  rw [same] at read
  exact read

end YM.Integration.WilsonRootedPhysicalCatalogue
