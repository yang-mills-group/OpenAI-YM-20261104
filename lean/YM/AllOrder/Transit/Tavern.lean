import YM.AllOrder.Transit.Crown
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
structure TicketP {X:Metals G} {D:Rolls X.p}(A:Alloy X D)(F:Factor A)
    (Ξ:Roots (G:=G) X.p.profile X.K X.p.kernel)(T':Ξ.Tab D):Prop where
    pledge : Pass Ξ T' A F
    head' : Header A.delay
def Station (A:Alloy X D)(F:Factor A):Prop:= ∃ (R:Roots (G:=G) X.p.profile X.K X.p.kernel)(Q:R.Tab D), TicketP A F R Q
variable (Xξ: Org.Bolt A)(hW:Graces.Nest F Xξ)(hQ: TicketP A F R Q) -- Ticket intr scope.Bu.Was `n` unbound implicit declarations.Seam
variable (W':ℕ→ Layout G)(Γ:ℕ→ Pace.Coin)(hP: Step.PlanV.Path R A Q (Burn.horizon k) N m W' Γ)
-- defined as function.Space top uses map.career.All Periods separate Notice Aal.. scalar.Actual.Reader.Last.Core costs.w1
abbrev finβ (k n N:ℕ)(ρ:Pace.Coin)(m:ℕ): ℝ:= Wheel.now ρ (Burn.horizon k+2) ((Xξ.history N n (m+1)).beta)
structure Rec (W':ℕ→Layout G)(Γ:ℕ→ Pace.Coin)(m N n k:ℕ)(x:(i:ℕ)→ RG.Rep G (A.B.a.S.side i n)) : Prop where
    start : A.B.bake.Starter N n (x N)
    walk : ∀ i:ℕ,m ≤ i → i ≤ N → Appearance A Xξ (W' i) i n N k (x i)
    visit : ∀ i:ℕ,m ≤ i → i < N → A.B.Move N i n (x i) (x (i+1))
    pace : ∀ i:ℕ,m ≤ i → i < N → (A.B.a.budget i).threshold^2*|(Xξ.history N n i).beta-finβ A Xξ k n N (Γ i) i|≤ PostP.θ2 G (X.p.profile (A.B.a.clock.J i)) (A.B.a.clock.hatBeta i) k
include hQ hP hk hW g0
theorem recur (hh:m≤N)(n:ℕ): ∃ x,Rec A Xξ W' Γ m N n k x:= by
 induction hh using Nat.decreasingInduction with
 | self=>
    obtain ⟨U,hK,hU⟩:= WheelP.started R Q A F hQ.pledge g0 hk (n:=n) Xξ hQ.head'; let x:=Function.update (Xξ.history N n) N U; refine ⟨x,⟨(show x N=U from update_self ..).symm ▸ hK,fun i hi hj=> ?_,fun i hi h=> by omega,fun i hi h=> by omega⟩⟩; rw [le_antisymm hj hi,hP.2.1, show x N=U from update_self ..]; exact hU
 | of_succ m hm ih=>
    have he:= le_trans hk (A.B.a.fits.mono (Nat.le_succ m)); let K:= (A.B.a.clock.hatBeta m); have hz:Step.PlanV.Path R A Q (Burn.horizon k) N (m+1) W' Γ:= ⟨fun i hi hj=> hP.1 i (by omega) hj,hP.2.1,fun i hi hj=> hP.2.2 i (by omega) hj⟩; obtain ⟨x,hx⟩:= ih he hz;
    obtain ⟨U,hh,ht,hB,hE,hΩ⟩:= hP.2.2 m le_rfl hm;
    have hv:= hx.walk _ le_rfl hm; rw [hB] at hv; obtain ⟨hp,Tξ,hc,hΨ⟩:= steps R Q A F hQ.pledge g0 hm hh U ht Xξ hW hv
    let v:= Function.update x m Tξ; have ht' : v m=Tξ:=update_self ..; have hi'(i)(h:m < i):v i=x i:= update_of_ne h.ne' ..; refine ⟨v,hi' N hm|>.symm ▸ hx.start,fun i hi hj=>?_,fun i hi hj=>?_, fun i hi hj=>?_⟩;
    · rcases lt_or_eq_of_le hi with he|rfl; · rw [hi' i he]; exact hx.walk _ he hj
      rw [ht',hE]; exact hΨ
    · rcases lt_or_eq_of_le hi with he|rfl; · rw [hi' i he,hi' (i+1) (by omega)]; exact hx.visit i he hj
      rw [ht',hi' _ (by omega)]; exact hc
    rcases lt_or_eq_of_le hi with he|rfl; · exact hx.pace i he hj
    rw [hΩ]; exact hp
variable (k N m)
-- same Q chosen before ANY allowed pressure.ct. ∃ used all horizons with certificate
omit hP
theorem tender (he:m≤N): ∃ W' Γ,Step.PlanV.Path R A Q (Burn.horizon k) N m W' Γ ∧ ∀ n:ℕ,∃ x, Rec A Xξ W' Γ m N n k x:= by
 obtain ⟨K,T0,hP⟩:= Step.PlanV.began R A F Q hQ.pledge.formal N m he hk; exact ⟨K,T0,hP,recur R Q A F g0 hk Xξ hW hQ K T0 hP he⟩
omit hQ hW hk g0
lemma Station.departs (h:Station A F) (Xξ:Org.Bolt A) (T₀:Graces.Nest F Xξ) (g0:G.Simple):∃ (R:Roots X.p.profile X.K X.p.kernel) (G' : R.Tab D), TicketP A F R G' ∧ ∀ (k m N:ℕ),(Burn.horizon k)+2≤A.B.a.clock.J m→ m≤N→ ∃ W' Γ,Step.PlanV.Path R A G' (Burn.horizon k) N m W' Γ ∧ ∀ n:ℕ,∃ x, Rec A Xξ W' Γ m N n k x:= by obtain ⟨R,Q,h⟩:= h; exact ⟨R,Q,h,fun k m N hk he=> @tender G X D R Q A F m k N g0 hk Xξ T₀ h he⟩
end WheelP
end YM.AllOrder.Transit
