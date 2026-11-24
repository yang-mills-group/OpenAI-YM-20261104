import YM.AllOrder.Transit.Tavern
import YM.QuadraticLocal.Cable
/-!
# Carrier station merry: ALL unmarked Repeat program jointly makes Marked alternative lane
normalization receipts. Extension proofs of Transit.Tavern. Not inferring convergence of whole
path here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Transit
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Bid Planned.JetPort PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Trio Lantern High
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm JointLoad.Clockwork
open Burn Carillon Cap
open Rosary.Repair
open Transit Transit.Moon Transit.Moon.Kit
open Floe Floe.StateE
open Step PlanV Roost
variable {G:Gauge}{X:Metals G}{D:Rolls X.p} (R: Roots (G:=G) X.p.profile X.K X.p.kernel) (Q:R.Tab D)(A:Alloy X D)(F:Factor A)
namespace WheelP
variable {m n k N:ℕ} (h:Pass R Q A F)
local notation "S"=> X.p
set_option quotPrecheck false
local notation "a"=> A.B.a
local notation "C"=> X.p.profile
local notation "E"=>A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.J (m+1)
local notation "V"=> A.B.a.budget m
local notation "y"=> A.B.a.clock.hatBeta m
local notation "L"=> D.L Y
local notation "t"=> betaF G y L
local notation "s"=> (C E)
local notation "W"=> A.B.a.budget (m+1)
local notation "B"=> radiusB y
local notation "g"=> A.B.a.S.block m
local notation "T"=> F.target Y E
local notation "P!"=> (F.expense Y E)
local notation "p"=> A.B.a.params m
local notation "z"=> Burn.horizon k
variable (g0:G.Simple)(hm:m<N)(hk:Burn.horizon k+2≤ A.B.a.clock.J m)
/- The all-order estimate through LEVEL recurrence at the same trajectory on arbitrary initial cutoff, in RG/Scheduled E and in full positions/projection. Cap horizon∼3*k+2. Compatibility when changing the horizon k is another question; not claimed here. Unit chosen by actual.Remainder Γ independent PT.S.
Not a statement about readout/conversion global β functional. -/
open Quay Floe Step.PlanV
variable (Xξ: Org.Bolt A)(hW:Graces.Nest F Xξ)(hQ: TicketP A F R Q) -- Ticket intr scope.Bu.Was `n` unbound implicit declarations.Seam
variable (W':ℕ→ Layout G)(Γ:ℕ→ Pace.Coin)(hP: Step.PlanV.Path R A Q (Burn.horizon k) N m W' Γ)
-- defined as function.Space top uses map.career.All Periods separate Notice Aal.. scalar.Actual.Reader.Last.Core costs.w1
abbrev Concourse (W':ℕ→Layout G)(Γ:ℕ→ Pace.Coin)(m N n k:ℕ)
   (x:(i:ℕ)→ RG.Rep G (A.B.a.S.side i n)):= Rec A Xξ W' Γ m N n k x ∧ ∀ i:ℕ,m≤ i → i < N → CarrierGuide A F i n N (x (i+1)) (x i)
variable (hg: QuadraticLocal.Beaming.Frost F.shape F.book F.scout A.delay)
include hQ hP hk hW g0 hg
theorem recur_lane (hh:m≤N)(n:ℕ): ∃ x,Concourse A F Xξ W' Γ m N n k x:= by
 induction hh using Nat.decreasingInduction with
 | self=>
    obtain ⟨U,hK,hU⟩:= WheelP.started R Q A F hQ.pledge g0 hk (n:=n) Xξ hQ.head'; let x:=Function.update (Xξ.history N n) N U; refine ⟨x,⟨(show x N=U from update_self ..).symm ▸ hK,fun i hi hj=> ?_,fun i hi h=> by omega,fun i hi h=> by omega⟩,fun i hi h=> by omega⟩; rw [le_antisymm hj hi,hP.2.1, show x N=U from update_self ..]; exact hU
 | of_succ m hm ih=>
    have he:= le_trans hk (A.B.a.fits.mono (Nat.le_succ m)); let K:= (A.B.a.clock.hatBeta m); have hz:Step.PlanV.Path R A Q (Burn.horizon k) N (m+1) W' Γ:= ⟨fun i hi hj=> hP.1 i (by omega) hj,hP.2.1,fun i hi hj=> hP.2.2 i (by omega) hj⟩; obtain ⟨x,hx,hy⟩:= ih he hz;
    obtain ⟨U,hh,ht,hB,hE,hΩ⟩:= hP.2.2 m le_rfl hm;
    have hv:= hx.walk _ le_rfl hm; rw [hB] at hv; obtain ⟨hp,Tξ,hc,hΨ,hΔ⟩:= car_steps R Q A F hQ.pledge g0 hm hh U ht Xξ hW hg hv
    let v:= Function.update x m Tξ; have ht' : v m=Tξ:=update_self ..; have hi'(i)(h:m < i):v i=x i:= update_of_ne h.ne' ..; refine ⟨v,⟨hi' N hm|>.symm ▸ hx.start,fun i hi hj=>?_,fun i hi hj=>?_, fun i hi hj=>?_⟩, fun i hi hj=>?_⟩;
    · rcases lt_or_eq_of_le hi with he|rfl; · rw [hi' i he]; exact hx.walk _ he hj
      rw [ht',hE]; exact hΨ
    · rcases lt_or_eq_of_le hi with he|rfl; · rw [hi' i he,hi' (i+1) (by omega)]; exact hx.visit i he hj
      rw [ht',hi' _ (by omega)]; exact hc
    · rcases lt_or_eq_of_le hi with he|rfl; · exact hx.pace i he hj
      rw [hΩ]; exact hp
    rcases lt_or_eq_of_le hi with he|rfl; · rw [hi' i he,hi' (i+1) (by omega)]; exact hy i he hj
    rw [ht',hi' _ (by omega)]; exact hΔ
variable (k N m)
-- same Q chosen before ANY allowed pressure.ct. ∃ used all horizons with certificate
omit hP
theorem tender_lane (he:m≤N): ∃ W' Γ,Step.PlanV.Path R A Q (Burn.horizon k) N m W' Γ ∧ ∀ n:ℕ,∃ x, Concourse A F Xξ W' Γ m N n k x:= by
 obtain ⟨K,T0,hP⟩:= Step.PlanV.began R A F Q hQ.pledge.formal N m he hk; exact ⟨K,T0,hP,recur_lane R Q A F g0 hk Xξ hW hQ K T0 hP hg he⟩
end WheelP
end YM.AllOrder.Transit
