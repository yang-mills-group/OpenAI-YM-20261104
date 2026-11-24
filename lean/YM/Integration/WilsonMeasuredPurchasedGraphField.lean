import YM.Integration.WilsonOlderFreshGraphAdjacent

/-! After-election comparison on the specified upper and lower posts at every
actual child, retaining any lower support and radius purchase on those posts. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPurchasedGraphField
open OPE.Therm
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G){m j N per k:ℕ} (query:WilsonOlderFreshGraphAllStages.Query)
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q₀:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q₀ φ)
  (floor:m ≤ j)

local notation "hi" => (floor.trans (Nat.le_succ j))
local notation "i₁" => (j+1)
variable
  (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N))
  (school:Syl.School k)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J ((j+1)+1)) (R.alloy.B.a.clock.J (j+1)))
  (lesson:Lesson (N:=N) R hk D Q₀ π Γ (floor.trans (Nat.le_succ j)))
  (cal:Oak.Calendar R hk D Q₀ π Γ Ψ (floor.trans (Nat.le_succ j)) (N:=N) lesson)
  (ahead:Mentor.Forecast D R.rolls Q₀ φ books)
  {ZΘ:ℝ} {profile:PhysicalNext.ThroughLaunch.Orders}
  (house:QuadraticLocal.Advent.Sycamore.Treehouse.VariableHouse R D Q₀ scroll books ZΘ ahead profile)
local notation "σ₀"=> Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i₁+1))
variable (A:Unit→Set ℂ)
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics

local notation "families" => (fun u:ℕ=>Flat.routes (R.family.path.levels.clock.op u 0).patch)
variable {dmax:ℕ} (a:hue G) (depth:query.letter.toll<dmax)
    (w:Letter (R.family.labels.level query.letter.toll)) (f:Studio dmax)
local notation "Ω₀"=>Oak.expenseReal R hk D Q₀ π Γ books hi op lesson ahead school.order school.horizon

local notation "βhat"=>R.alloy.B.a.clock.hatBeta (i₁+1)
local notation "massF"=>‖Annex.compress dmax f‖


variable (base:Site (R.family.side (j+1) per))
local notation "child" => Site (R.family.path.levels.S.block (j+1))
local notation "place" => fun z:child=>(R.family.path.levels.clock.op (j+1) per).ratio.assemble (base,z)
local notation "testAt" => fun z:child=>Dawn.throughW z dmax (Elm.growL R.family.path.levels (j+1)) f
local notation "salary" => fun z:child=>1+‖Annex.compress dmax (testAt z)‖
local notation "slate" => WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order σ₀
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N per j
variable (p:ℕ) {ε:ℝ} (ep:0 < ε)
local notation "q₁" => (p+2+2)
private theorem divide_pos {ε:ℝ} (ep:0 < ε) : 0 < ε/16 := div_pos ep (by norm_num)
local notation "ep₀" => divide_pos ep

private theorem ready_order {q J:ℕ} (h:2*(q+4+1)+8 ≤ J) : 2*q+8 ≤ J := by omega
private theorem ready_age {q k:ℕ} (h:q+4+4 ≤ 3*k+2) : q+3 ≤ 3*k+2 := by omega

local notation "upperSide" => R.family.side ((j+1)+1) per
local notation "lowerSide" => R.family.side (j+1) per
local notation "stock" => Stock.census Unit
local notation "u" => (Stock.census Unit).fire ()
local notation "kernel" => (fun _ : Unit => (⊥ : Submodule ℝ ℂ))
local notation "grades" => (fun _ : Unit => query.letter.toll)
local notation "birth" => fun (z:child) (T:slate) (t:Wallet A) (U:Config G upperSide) =>
  ((Ψ ((j+1)+1)).eval U:ℂ) • Poly.pass (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A)
    (Coat.gStep (Ψ ((j+1)+1)).beta) t U)
local notation "down" => fun z (T:slate) (t:Wallet A)=>LocalComparison.actualPush R.family N per (j+1) (birth z T t)
local notation "lower" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces j floor (down z T)
local notation "origin" => fun z:child=>((Earn.Passport.point (fun _:Unit=>place z)).coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin ()
local notation "rp" => Ψ (j+1)
local notation "F₁" => R.family.labels.level query.letter.toll
local notation "section₁" => R.family.localSection query.letter.toll
local notation "κ" => LocalComparison.forcedDivisor R.family (j+1)
local notation "gl" => Coat.gStep (Ψ (j+1)).beta


local notation "passports" => fun z:child=>Earn.Passport.point (fun _:Unit=>place z)
local notation "upper" => fun z (T:slate)=>Post (V:=Unit) (X:=fun _=>ℂ) (N:=N) R hk D Q₀ π Γ Ψ books ahead
  A kernel grades school.order school.horizon school.pieces (j+1) (floor.trans (Nat.le_succ j)) (birth z T)



local notation "blockSide" => R.family.path.levels.S.block (j+1)
local notation "rate" => (((blockSide).val:ℝ)^query.letter.toll/((blockSide).val:ℝ)^4)

local notation "gu" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "material" => fun (z:child)(T:slate)(t:Wallet A)(U:Config G upperSide)=>
  (Spill.Foundry.uncut (T.rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) gu t U).part u
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages
include history scroll top house ep in
theorem fromPurchased (simple:G.Simple) (cut:i₁<N) (cap:∀t,‖value A t‖≤1)
    (lateScene:WilsonOlderFreshGraphFundedScene.opening R school ≤ j)
    (enrolled:query.order ≤ school.order) (high:ℕ)
    (space:Sycamore.Boot.need high school ≤ R.alloy.B.a.clock.J (i₁+1))
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon k) N m π Γ)
    (month:Scholar.Month R.rolls D Q₀ R.alloy.delay)
    (narrow:school.horizon ≤ R.alloy.B.a.clock.J i₁) (pace:WilsonWindowReportingPace.Slow R.kit)
    (money:WilsonMeasuredLandedCurrency.first R simple ≤ j)
    (geometry:WilsonOlderFreshGraphPreimageFee.first R simple pace query.letter.toll ≤ j+1)
    {bound:ℕ→ℕ} (formal:WilsonWindowFormalPurchase.Canonical bound R.kit)
    (probes:Loc G 1) (v:ℕ→Gear G→ℝ) (funded:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)
    (fundedDate:WilsonOriginalPrimerPostCover.opening R simple v funded paths k ≤ m)
    (passport:Pass D Q₀ R.alloy R.kit) (fits:school.order ≤ Burn.horizon k+1)
    (hd:query.letter.toll ≤ R.family.path.levels.clock.J ((j+1)+1)) (width:0 < σ₀)
    (T:child → slate) (H:∀z:child,upper z (T z)) (F:∀z:child,lower z (T z))
    (published:∀z:child, WilsonOlderFreshGraphDatedSalary.Published R families a depth (i₁+1)
      w ⟨⟨N,cut⟩,testAt z⟩ (T z))
    (issued:∀z:child,(H z).passport=passports z ∧ (H z).modelIndex=(T z).Roster ∧
      HEq (H z).model ((T z).rows (WilsonOlderFreshGraphPointWallet.point (place z)) A) ∧
      Filed R hk D Q₀ π Γ Ψ books ahead A kernel grades school.order school.horizon school.pieces
        floor (birth z (T z)) (H z) (F z))
    (bills:∀z:child, ∀t:Wallet A, ∃(E:Coefficient F₁ lowerSide)(b:ℝ),
      E.Format (origin z) R.family.params rp ∧ E.remBound (origin z) rp κ b ∧
      (∀U,E.density (origin z) section₁ rp U=(down z (T z) t U).part u-
        ((rp).eval U:ℂ)*(Spill.Foundry.uncut (F z).model gl t U).part u) ∧
      b+(F₁).coeffSize E.x ≤ ε*g₀^(p+2)*(salary z)) :
      (∀{σ':ℝ}(T₀:Letter (R.family.labels.level query.letter.toll) →
                WilsonOlderFreshGraphSlate.Copy G query.letter.toll query.order σ'),0<σ' →
          (∀v,WilsonOlderFreshGraphDatedSalary.Published R families a depth i₁ v ⟨⟨N,cut.le⟩,f⟩ (T₀ v)) →
          ∀(t:Wallet A)(e:ℕ),e≤query.order → ∀B:Stationary.Link G lowerSide,
        (Kemp.aven (R.family.path.levels.S.block (j+1)) query.letter.toll:ℂ)*
          ∑z:child,(peek dvd_rfl (F z).model grades (π (j+1)) (Step.tape (Burn.horizon k+2)) t e B).part u =
        ∑v:Letter (R.family.labels.level query.letter.toll),
          ∑lag∈(_root_.Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
            ((PowerSeries.coeff lag.1 (Primer.fieldStep R.family a families depth N i₁ v w):ℝ):ℂ)*
            (peek dvd_rfl ((T₀ v).rows (WilsonOlderFreshGraphPointWallet.point base) A) grades (π i₁)
              (Step.tape (Burn.horizon k+2)) t lag.2 B).part u) ∧
      ∀(t:Wallet A)(h:child → ℂ), (∀z,‖h z‖ ≤ rate) → ∃(E:Coefficient F₁ lowerSide)(b:ℝ),
        E.Format base R.family.params rp ∧ E.remBound base rp κ b ∧
        (∀U,E.density base section₁ rp U=(∑z,h z*(down z (T z) t U).part u)-
          ((rp).eval U:ℂ)*(∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u)) ∧
        (∀U,((rp).eval U:ℂ)⁻¹*E.density base section₁ rp U =
          actualAverage R.family (N:=N) (fun V=>∑z,h z*(material z (T z) t V)) U-
          ∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u) ∧
        ( (∫ U,((rp).eval U:ℂ)⁻¹*E.density base section₁ rp U ∂scene R.family.path N per (j+1)) =
            (∫ V,∑z,h z*(material z (T z) t V) ∂scene R.family.path N per ((j+1)+1))-
              (∫ U,∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u ∂scene R.family.path N per (j+1))) ∧
        b+(F₁).coeffSize E.x ≤ (8*ε)*g₀^p*(1+‖Annex.compress dmax f‖):=by
  constructor
  · intro σ' T₀ σpos named t e he B
    have formalRow:=WilsonNeutralFundedFieldTable.original (R:=R) (hk:=hk) (D:=D) (Q:=Q₀) (π:=π) (Γ:=Γ) (Ψ:=Ψ)
      (course:=history) (books:=books) (ahead:=ahead) (floor:=floor) (cut:=cut)
      (actors:=A) (pieces:=kernel) (color:=a) (pad:=depth) (grant:=formal) (base:=base) (b:=w) (f:=f)
      (T:=T) (H:=H) (F:=F) (filed:=fun z=>(issued z).2.2.2)
      (passport:=fun z=>(issued z).1) (names:=fun z=>(issued z).2.1) (rows:=fun z=>(issued z).2.2.1)
      (cap:=cap) (width:=width) (published:=published)
      (pass:=passport) (month:=month) (fits:=fits) (narrow:=narrow) (hs:=simple)
      (o:=probes) (v:=v) (funded:=funded) (paths:=paths) (opening:=fundedDate)
      (path:=path) (working:=enrolled) (hd:=hd) (t:=t) (e:=e) (he:=he) (B:=B)
    refine formalRow.trans ?_
    let binder:=WilsonOlderFreshGraphPointWallet.point base
    have root:=WilsonNeutralDatedChildPosition.point base
    have seen:=WilsonOlderFreshGraphLowerConvolution.original (d:=query.letter.toll) (kept:=query.order)
      (D:=dmax) (N:=N) (i:=j+1) (σ:=σ') R families a depth formal simple probes cut.le hd w f T₀
      binder A cap σpos named (π (j+1)) (Step.tape (Burn.horizon k+2)) t e he B
    simpa only [binder,root.1,root.2] using seen
  · intro t h hw
    let lim:child→ℝ:=fun z=>ε*g₀^(p+2)*(salary z)
    obtain ⟨E,b,form,rem,physical,price⟩:=WilsonOlderFreshGraphOriginalChildSum.original R hk D Q₀ π Γ Ψ
      history books floor school ahead A base cut T F t h lim (fun z=>bills z t)
    have gp:0<g₀:=(WilsonMeasuredLandedCurrency.native R simple per cut.le money).2.1
    have bound:=WilsonOlderFreshGraphPreimageFee.original R simple pace cut.le money query.letter.toll p
      geometry (by positivity : 0 ≤ 8*ε) f lim h hw
      (fun z=>by dsimp only [lim];rw [show 8*ε/8=ε by ring])
      (fun z=>by dsimp only [lim];positivity)
    have conditional (U) : ((rp).eval U:ℂ)⁻¹*E.density base section₁ rp U =
        actualAverage R.family (N:=N) (fun V=>∑z,h z*(material z (T z) t V)) U-
          ∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u := by
      have sum:=WilsonOlderFreshGraphChildAverage.original R hk D Q₀ π Γ Ψ history scroll books
        house.licence.employed floor house.stamps top school ahead A base cut T high space
        (fun z=>⟨H z,(issued z).1,(issued z).2.1,(issued z).2.2.1⟩) t h U
      have dn:(rp).eval=(R.family.path.rep N per (j+1)).eval:=
        (history.1.walk (j+1) (floor.trans (Nat.le_succ j)) cut.le).view
      have posW:(((rp).eval U:ℝ):ℂ)≠0:=by
        rw [dn]; exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson cut.le U).ne'
      let z₀:ℂ:=(rp).eval U
      let v:ℂ:=actualAverage R.family (N:=N) (fun V=>∑z,h z*(material z (T z) t V)) U
      let n:ℂ:=∑z,h z*(down z (T z) t U).part u
      let l:ℂ:=∑z,h z*(Spill.Foundry.uncut (F z).model gl t U).part u
      have paid:E.density base section₁ rp U=n-z₀*l:=physical U
      have integral:z₀*v=n:=sum
      change z₀⁻¹*E.density base section₁ rp U=v-l
      rw [paid,←integral,←mul_sub,←mul_assoc,inv_mul_cancel₀ posW,one_mul]
    refine ⟨E,b,form,rem,physical,conditional,?_,price.trans bound⟩
    exact WilsonOlderFreshGraphOriginalScene.original R hk D Q₀ π Γ Ψ history scroll books
      house.licence.employed floor house.stamps top school ahead A base cut T F high space
      ((WilsonOlderFreshGraphFundedScene.lower_appointment R school).choose_spec j lateScene)
      (fun z=>⟨H z,(issued z).1,(issued z).2.1,(issued z).2.2.1⟩) t h _ conditional

end YM.Integration.WilsonMeasuredPurchasedGraphField
end
