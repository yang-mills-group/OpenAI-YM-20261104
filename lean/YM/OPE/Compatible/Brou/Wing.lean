import YM.OPE.Compatible.Month.Goblin
import YM.OPE.Compatible.Brou.Arc
import YM.OPE.Compatible.Brou.Pole
import YM.OPE.Compatible.Brou.Bands
/-!
# Gates and money presented by actual track. Receipt form. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open RG RG.Shoot RG.Supply Input Org Extra.Histories
open Next.Scheduling Mallow Graces Legato Roost PriceCompiler
open Next.Rank.Thirst YM.OPE
open scoped Topology Interval InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{W a σ C κ v γ t s w:ℝ} {m N p i j k:ℕ}
-- scene receipt.F
variable {X:Metals G}{D:Rolls X.p}{A:Alloy X D}(R:Factor A){u: Clip} -- optional
-- selected positivity duplicate, careful import UVExt not accepted? adapt
private lemma weightP (H0:History G)(h:H0.Selected) {N m p :ℕ} (hm:m ≤ N)(V:Config G (H0.S.side m p)):0 ≤ (H0.rep N p m).eval V:=by
  suffices ∀ m, m≤N → ∀ V : Config G (H0.S.side m p), 0 ≤ (H0.rep N p m).eval V by exact this m hm V
  refine fun m hm => Nat.decreasingInduction (motive:=fun k _ => ∀ V : Config G (H0.S.side k p), 0≤(H0.rep N p k).eval V) ?_ ?_ hm
  swap; · rw [(h.starts N p).2]; exact fun V => (bare_pos _ V).le
  intro k hk ih V; rw [(h.steps N p k hk).1]; exact integral_nonneg fun U=> mul_nonneg ((H0.levels.transition_mass ..).positive U V) (ih U)
-- type L.Dom Seats
variable (g:G.Simple)(z:Patch)(b: Arms (M:=X) D)(T:Bolt A)(H:Nest R T)
local notation "A*"=>A.B.a
local notation "Jι"=> A.B.a.clock.J
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Kι"=> A.B.a.clock.J m
local notation "K!"=> A.B.a.clock.hatBeta
local notation "Nm"=> T.history N p m
local notation "Mm"=> T.history N p (m+1)
local notation "Wm"=> A.B.a.clock.op m p
local notation "Bm"=> A.B.a.budget m
variable (hp: R.books=b)(hm:m<N)
include H hm g
lemma πreset : (A.B.a.budget m).threshold^2 * |(Nm).beta-(Mm).beta-A.B.kin.alpha N m|≤ AnalyticBridge.VerifiedReset.Time.forecastE A.B.a m:= by
   obtain ⟨l,v,Q,Y,x,hx,hq,hN⟩:= (H.held N m p hm).1; rw [hN,hq]; have he:= (Y.moves g hm).2 x hx|>.2.2.1; dsimp only [UVNext.CouplingReset.predictor] at he; rw [show (Y.result x).beta- _-_=_ from (sub_add_eq_sub_sub ..).symm]; exact he
section
omit g hm
lemma candy (hn:m<N):WilsonStartup.Decent (Nm).clip (Nm).p:=by
  obtain ⟨l,v,Q,Y,x,hx,-,-⟩:= (H.held N m p hn).1
  have he:= (T.sticks N p).prices m (Nat.zero_le _) hn.le|>.1; rw [he.point,he.clip]; exact (R.machine.passes hn Y.knows).1.decent
end
-- Receipt fixed parameters need T coverage
variable {c f:Side}
def epoch (b:Arms (M:=X) D) (z:Patch)(j i:ℕ) {c f:Side}(S:StepData c f)(T':Tube G S)(x:ℝ)(R':RG.Rep G f):Prop:= foam (b.target j i) (D.L j) ∧ z.Branches X.p.kernel G ∧ (Pressure.Testing.query X.p X.K j i).bind=X.p.kernel∧ (0<(b.shape.μ j i)) ∧ S.patch=z∧ Stamp T' ∧ HasSlots R'.p R'.activities ∧(∀ U,0≤R'.eval U)∧ WilsonStartup.Decent R'.clip R'.p ∧
        ∃ H:Cash (b.walls j i) x (b.shape.μ j i) (D.L j) (b.target j i) (b.shape.o j i) (b.shape.c j i) T' R',Cash.Renewed (b.expense j i).degrees (b.expense j i).earn (b.expense j i).one (b.expense j i).two H
section
omit hm
include hp
lemma enact {Y:ℕ→ℝ}{q: Worth}(a:Legato.Bandage R Y q)(hZ:(Wm).patch=z)(hJ:J=j)(h':Kι=i)(hk:m+1<N): epoch b z j i (Wm) (Pressure.Testing.ships A.B N m p) (K! m) (Mm):=by
    subst i j b z
    obtain ⟨l,v,Q,Y0,x,hx,hΓ,hH⟩:= (H.held N m p (by omega)).1
    let z:=(Wm).patch; let P:= Pressure.Testing.query X.p X.K J Kι; have he:P.bind=X.p.kernel:=rfl
    refine ⟨(a.r _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).1.1,X.p.has z,he,(R.shape.consumes J Kι (step_paid A.B.a m)).2.1,rfl,Opera.protocol A.B (by omega) R.pledging.conducts.full, H.samples g _ _ _ hk.le,weightP _ T.choice hk.le, candy R T H hk,?_⟩
    rw [hΓ]; let B: Set.Icc l v:= ⟨x,hx⟩; exact ⟨Y0.H.houses B,Y0.H.honors B⟩
end
end YM.PhysicalNext.Repeat.Aroma
