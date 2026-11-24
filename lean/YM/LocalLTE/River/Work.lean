import YM.LocalLTE.River.Pulp
/-! Basin. Price of operating block transfer on arbitrary existing stage.
What is important is **worked**: the proof at unchanged scale for ANY
admissible input of that support is in the SAME chosen canonical cloud.Turn.
Not merely some presentation of it guaranteed via physical kernel norm.
Forecast's selected workspace does not constrain this.Duplicates h etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Turf
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
variable (hC:Mallow.Arrives R.shape A.delay) (hM : Graces.Moms R.prices M.K R.span M.p.floorL)(hV: Graces.Cruise R.prices D R.recordP R.span R.shape A.delay) (hd:d+3 ≤ A.B.a.clock.J m) {K:ℕ → ℝ}{W:Bid.Worth}(hp : Doors.Budget A.B.a K W)(hh : Graces.Comply R.shape A.delay)
variable (U : Turf R N m n)
    (hr : (Issue.trail Z).rep N n (m+1)= U.inPort) (hℓ: (Issue.trail Z).rep N n m=U.output) (hΘ:HasSlots U.inPort.p U.inPort.activities)
open YM.MergeProof
local notation "R'"=> U.inPort
local notation "tu"=> localSection G d
set_option quotPrecheck false
local notation "V!"=> U.door
local notation "sandbox"=> U.houseB
local notation "Rπ"=> duet _ _ _ _ hℓ hr V!
local notation "cX"=> A.B.a.S.side (m+1) n
local notation "z'"=> (((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d)
local notation "δ"=> (Real.sqrt (A.B.a.clock.forcedAllowance m))
local notation "Xa" T => Blush.scope U.houseB (T) (0:Site (A.B.a.S.side m n))
local notation "P'" T => Blush.screen U.houseB T (U.lamp (T|>.live)) (U.lamp (T|>.pale)) ((((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d)) ((Labels.frames G).level d)
include hp hd hℓ
open Graces
local notation "sI" => A.B.a.clock.forcedAllowance m
open LocalLTE.River -- maybe qualification
private lemma cone (T:Cloud U.inPort)(v u:ℝ) (f:Config G (A.B.a.S.side (m+1) n)→ℂ)(h:Fancy (localSection G d) H N n m (hol G) f (Xa T) (P' T) 0 (authors A.B.a m) v u):Planned.GuardedAtom.Deck (P' T) 0 (Xa T) U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) u u:=by
    obtain ⟨a,b,q,⟨hf,hW⟩,hy,hs,⟨x,y,h₀,hT⟩,he,hQ⟩:= h
    have hh : d ≤ i₀:= (Nat.le_add_right d 3).trans hd
    have hU := Graces.livelyCard hp hh (n:=n)
    let t:=(P' T); have hF:0<δ:=Real.sqrt_pos.mpr (Extra.Histories.forcedPos A.B.a m)
    simp only [Push.Local.kappa] at hs h₀; rw [hℓ] at hf hW hQ hs h₀ hT he
    have hκ:1 ≤ Local.factor (hol G) (localSection G d) U.output.p.supportExponent (authors A.B.a m):= LocalLTE.Dilation.factorLarge hU
    obtain ⟨ha,hb,hq⟩:= Tare.costs_nonneg hs hF
    have hx:0≤x:= (h₀.costs_nonneg hF).1
    have hp : a ≤ Local.turnCost U.output.p.order U.output.p.power*a:= le_mul_of_one_le_left ha (LocalLTE.River.turn_one ..)
    have hi : x ≤ a:= hT ▸ le_mul_of_one_le_left hx hκ
    constructor
    · obtain ⟨c,hc,hX⟩:= h₀.bulk; exact ⟨c,hc,hX.1,hX.2.1,hX.2.2.trans (by linarith only [he,hi,hp,hq,hb])⟩
    obtain ⟨c,hb',hp'⟩:= hs.packets; exact ⟨c,⟨hb'.1,hb'.2.1,hb'.2.2.trans (mul_le_mul_of_nonneg_left (by linarith only [he,hq,hp,ha]) hF.le)⟩,hp'⟩
include hC hh hr h g hm hΘ hp
include hM hV in
lemma ruled (b : Support (A.B.a.S.side (m+1) n)) (c:ℝ)(f:Config G (A.B.a.S.side (m+1) n)→ℂ) (hf: RegFit U.inPort 0 d (hol G) b f)(hB:U.inPort.p.supBounds 0 b f c): let C:=float U.inPort 0 b hf.anchor f c hf.smooth hB hΘ; let u:=Doors.rate L₀*(U.inPort.p.mass b c); Planned.GuardedAtom.Deck (P' C) 0 (Xa C) U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) u u:=by
   intro C t; exact U.cone hd hp hℓ C t t (Extra.Histories.salary U.inPort b f) (Graces.regularCardT g hm h hC hM hV hd hp hh U hr hℓ hΘ b c f hf hB) -- order
omit hΘ in
lemma worked (s:ℕ) (C:Config G (A.B.a.S.side (m+1) n)→ℂ)(a:ℝ) (hc:C≠0)(hX:SlotFit U.inPort 0 s C)(hA:∀ t,‖C t‖≤a):let F':=Blush.fan U.inPort 0 s C a hA hX; let u := Doors.rate L₀*(U.inPort.p.mass (U.inPort.activities.forced s).support a);Planned.GuardedAtom.Deck (P' F') 0 (Xa F') U.output (Real.sqrt (A.B.a.clock.forcedAllowance m)) u u :=by -- even UNdivided
   intro F' t; let y:= U.inPort.p.mass (U.inPort.activities.forced s).support a
   have hv := support_zero (N').ratio _ (show 0 ∈ F'.live.crest from hX.tagged hc); have hg:= glyphBound A.B.a (m+1)
   have hf:0≤y:= mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hA 1))
   let B':=U.houseB
   have hx: ∃ s': B'.fragrances → ℝ, SumBudget (fun i=> Local.reservedMass (A.B.a.budget m) (locus F'.live B' 0 i) (s' i)) (coinFee G (M.p.profile i₀) d L₀*y) ∧ ∀ i,prince F'.live B' i→ (A.B.a.budget m).supBounds 0 (locus F'.live B' 0 i) (pane B' F' z' i) (s' i):=by
      refine ⟨(fun i=>0),?_,fun i hi=> (never B' F'.live s rfl i hi).elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) hf)
   have hh' : d≤ i₀:=by omega
   exact U.cone hd hp hℓ F' t t F'.milk (sendsCardT g hm h hC U hℓ hr hp hh hh' F' hv hx le_rfl)
end YM.PhysicalNext.Repeat.Mallow.Turf
