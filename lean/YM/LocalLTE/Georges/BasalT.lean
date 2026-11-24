import YM.MergeProof.Basal
import YM.LocalLTE.Georges.Mile
import YM.LocalLTE.Georges.ThimbleT
import YM.LocalLTE.Georges.ElderT
/-! Adaptation of YM/MergeProof/Basal; same budget on Career. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}{B:BudgetPoint}{X:Support c}{f:Config G c→ℂ} {o:Site c}
variable (g:G.Simple) {M : Metals G} {D:Rolls M.p} {A:Alloy M D}
    {R: Factor A} {l v:ℝ} {N m n k d:ℕ} (hm:m<N) {Z:Bolt A} (h: HasSlots ((Issue.trail Z).rep N n m).p ((Issue.trail Z).rep N n m).activities) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "L₀" => D.L j₀
local notation "f₀"=> A.B.a.clock.hatBeta m
local notation "P" => M.p.profile i₀
local notation "pT" => R.prices j₀ i₀
local notation "S0" => ships A.B N m n
local notation "N'" => A.B.a.clock.op m n
local notation "O" => Chi.canonical
local notation "V" => A.B.a.S.side m n
set_option quotPrecheck false
local notation "U!" => ((H).rep N n (m+1))
local notation "O'" => ((H).rep N n m)
local notation "ip"=> A.B.a.params m
variable (hC:Mallow.Arrives R.shape A.delay) (hM : Moms R.prices M.K R.span M.p.floorL)(hV: Cruise R.prices D R.recordP R.span R.shape A.delay) (hd:d+3 ≤ A.B.a.clock.J m) {K:ℕ → ℝ}{W:Bid.Worth}(hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
include hp hd g hC hM hV hh h hm
variable (ht' : Turf R N m n)
    (hr : (Issue.trail Z).rep N n (m+1)= ht'.inPort) (hℓ: (Issue.trail Z).rep N n m=ht'.output) (hΘ:HasSlots (ht'.inPort|>.p) (ht'.inPort|>.activities))
include hr hℓ
open YM.MergeProof
local notation "R'"=> ht'.inPort
local notation "tu"=> localSection G d
set_option quotPrecheck false
local notation "V!"=> ht'.door
local notation "Rπ"=> duet _ _ _ _ hℓ hr V!
include hΘ
lemma basalCardT (b : Support (A.B.a.S.side (m+1) n)) (c:ℝ)(f:Config G (A.B.a.S.side (m+1) n)→ℂ) (hf: RegFit ht'.inPort 0 d (hol G) b f)(hB:ht'.inPort.p.supBounds 0 b f c)(Pa:Wing→Prop)(htV:Pa (.logKey (Blush.found 0 b hf.anchor))):
    let u:=ht'.inPort.p.mass b c; let t:=Doors.rate L₀ *u; let α:= masked (ht'.inPort|>.p.threshold) b f
    Coupon tu H N n m (hol G) α 0 0 Rπ Pa (Extra.Histories.salary ht'.inPort b f) 0 t t (2*u):=by
   intro u t α; let T:=float ht'.inPort 0 b hf.anchor f c hf.smooth hB hΘ
   have hZ:T.live.crest=b:=by change (ht'.inPort.activities.reg (found 0 b hf.anchor)).support=b; rw [Blush.latch _ _ _ _ hΘ]
   have hx:u=load T.live:=by unfold load; rw [hZ];rfl
   have hv:d ≤ i₀:= (Nat.le_add_right d 3).trans hd
   rw [hx]; apply thunderT g hm hC ht' hℓ hr hp hv T Pa htV (hZ.symm ▸ hf.anchor) _ α 0 t t 0 ?_ ?_ (regularCardT g hm h hC hM hV hd hp hh ht' hr hℓ hΘ b c f hf hB)
   · funext i; change _=(↑(Complex.reCLM (α i)):ℂ)+Complex.I*↑(Complex.imCLM (α i));rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
   funext j i; change (0:ℂ)=0+Complex.I*0; simp
end YM.PhysicalNext.Repeat.Graces
