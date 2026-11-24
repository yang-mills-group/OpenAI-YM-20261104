import YM.Integration.WilsonNeutralPointForecast
import YM.Integration.WilsonNeutralPointWeakForecast

/-! Every fixed physical test, coupling grade and moment reaches the two pointed budgets at the actual adjacent stages. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedPointedRequests
open Filter Lattice RG Wilson Precision PhysicalNext PhysicalNext.Repeat.Legato
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Quire Labels Source
open Stationary Exterior PowerSeries Tree Wilson Reef Jets Orb Wick Flat Next.Free
open scoped Classical

def load (d D e r l w:ℕ):ℕ:=d+D+e+r+l+max w ((d+1)*(d+1))+4

def exponential {G:Gauge} {j t:ℕ} (d D e r l w:ℕ)(admit:load d D e r l w≤j)(step:t≤j)
    (o:Loc G 1):WilsonNeutralPointAppointment.Request G j :=
  ⟨⟨d,by unfold load at admit;omega⟩,⟨D,by unfold load at admit;omega⟩,
   ⟨e,by unfold load at admit;omega⟩,⟨r,by unfold load at admit;omega⟩,
   ⟨l,by unfold load at admit;omega⟩,⟨t,Nat.lt_succ_of_le step⟩,o⟩

def polynomial {G:Gauge} {j t:ℕ} (d D e r l w:ℕ)(admit:load d D e r l w≤j)(step:t≤j)
    (o:Loc G 1):WilsonNeutralPointWeakAppointment.Request G j :=
  let c:=exponential d D e r l w admit step o
  ⟨c.field,c.test,c.grade,c.rank,c.slots,c.stage,
   ⟨max w ((d+1)*(d+1)),by unfold load at admit;omega⟩,o⟩

variable {G:Gauge}(R:Run G)(d D e r l w:ℕ)
local notation "A" => R.family.path.levels
local notation "K" => R.metals.p.kernel
local notation "W" => Borough.windowBasis G K
local notation "F" => (Labels.frames G).level
local notation "edge" i:max => (A).fits.mono (Nat.le_succ i)

theorem original (h:d<D)(strong:WilsonNeutralPointForecast.Filed R.kit)
    (weak:WilsonNeutralPointWeakForecast.Filed R.kit) :
    ∀ᶠ i:ℕ in atTop,∃ admit:load d D e r l w≤(A).clock.J (i+1),∀ o:Loc G 1,
    ∀ (per:ℕ)(S:Lodge (((A).clock.op i per).patch)), ∃ b c:ℝ,
     b≤Borough.ageZ ((A).clock.hatBeta i) ∧ c≤Borough.ageZ ((A).clock.hatBeta i) ∧
     WilsonNeutralPointAppointment.fits K F W (exponential d D e r l w admit (edge i) o) ((A).clock.op i per).patch S b ∧
     WilsonNeutralPointWeakAppointment.fits K F (polynomial d D e r l w admit (edge i) o) ((A).clock.op i per).patch S c := by
  have deep:Tendsto (fun i:ℕ=>(A).clock.J (i+1)) atTop atTop:=(A).fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [deep.eventually_ge_atTop (load d D e r l w)] with i admit
  refine ⟨admit,?_⟩
  intro o per S
  let x:=exponential d D e r l w admit (edge i) o
  let y:=polynomial d D e r l w admit (edge i) o
  have room:d+1≤(A).clock.J (i+1)-2:=by unfold load at admit;omega
  have money:(W).width ((A).clock.J i)≤Quire.coverPrice G K ((A).clock.J (i+1)) ((A).clock.J i):=
    ((W).lines (edge i) ((A).fits.stepSlow i)).2.2
  have sx:WilsonNeutralPointAppointment.ready K W x:=
    ⟨h,(A).clock.adm _,room,(A).clock.adm _,(W).pos _,(W).pos _,money⟩
  have sy:WilsonNeutralPointWeakAppointment.ready K W y:=
    ⟨le_max_right _ _,h,(A).clock.adm _,room,(A).clock.adm _,(W).pos _,(W).pos _,money⟩
  obtain ⟨b,hb,bx⟩:=WilsonNeutralPointForecast.original R strong i x S sx
  obtain ⟨c,hc,cy⟩:=WilsonNeutralPointWeakForecast.original R weak i y S sy
  exact ⟨b,c,hb,hc,bx,cy⟩

end YM.Integration.WilsonEmittedPointedRequests
end
