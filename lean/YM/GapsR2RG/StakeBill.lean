import YM.GapsR2RG.FullReserve
-- Exposing additional inputs implicit in the FullVolume.Panel event proofs.
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
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N)  {meshT :ℕ→∀ p, Trail A.B.a p} (choice : (A.B.bake.make meshT).Selected) {Q: In A.B.a m n}
local notation "H" => A.B.bake.make meshT
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "Q'" => R.target j₀ i₀
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "f₀"=>A.B.a.clock.hatBeta m
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "ξ" => (R.shape.μ j₀ i₀)
local notation "T₀" => YM.Labels.frames G
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (A.B.bake.make meshT).rep N n m = U.result x.val) (ht: (A.B.bake.make meshT).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
    (hd : d ≤ A.B.a.clock.J m) (T:Cloud (Q x)) (hω: (0:Site (A.B.a.S.side m n))∈T.live.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "T!" => houseS U x
local notation "V₁" => pupil U x T.live
local notation "V₂" => pupil U x T.pale
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "X!" => Blush.scope (T!) T o
local notation "M" => Blush.screen (T!) T V₁ V₂ v' F
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "fi" => coinFee G P d L₀ -- ambig
local notation "vh" => vigors G P d
include hd hp
open MergeProof
local notation "sandbox" => sandboxK U x
omit hd hp

include hd hp in
lemma stakeDebit {f:Config G (A.B.a.S.side (m+1) n)→ℂ}{v t:ℝ}{v₁:(F).Coeff} (S₀:Guard.Keeper ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities)
   (hY: MergeProof.Fancy (localSection G d) (A.B.bake.make meshT) N n m (hol G) f (X!) M v₁ w t v)(hv: (A.B.bake.make meshT).Conv N n m) : Staked (eventK U x T (d:=d) S₀) O v := by
  have hR : Local.Readable (hol G) (localSection G d) (O).p (A.B.a.S.side m n) w:= (hv.vac.symm ▸ (livelyCard hp hd (n:=n) ): Local.Readable _ _ _ (A.B.a.S.side m n) _)
  exact fancyStaked hY _ hR
end YM.PhysicalNext.Repeat.Graces
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {meshT:ℕ →∀ p, Trail A.B.a p} (h: HasSlots ((A.B.bake.make meshT).rep N n m).p ((A.B.bake.make meshT).rep N n m).activities) (choice: (A.B.bake.make meshT).Selected) {Q: In A.B.a m n}
local notation "H" => A.B.bake.make meshT
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "Q'" => R.target j₀ i₀
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "f₀"=>A.B.a.clock.hatBeta m
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "ξ" => (R.shape.μ j₀ i₀)
local notation "T₀" => YM.Labels.frames G
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (A.B.bake.make meshT).rep N n m = U.result x.val) (ht: (A.B.bake.make meshT).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
    (hd : d ≤ A.B.a.clock.J m)
set_option quotPrecheck false
open MergeProof
local notation "cX" => A.B.a.S.side (m+1) n
local notation "sandbox" => sandboxK U x
local notation "vb" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "RT"=> Q x
local notation "tu"=> (localSection G d)
local notation "q1" => duet (A.B.bake.make meshT) N n m he ht sandbox
include hC g hm hp hd hh he ht h choice
lemma heavyStake (s:ℕ) (C:Config G (A.B.a.S.side (m+1) n)→ℂ)(a:ℝ) (hc:C≠0) (hX:SlotFit (Q x) 0 s C)(hA:∀ t,‖C t‖≤a): let d':= (RT).p.mass ((RT).activities.forced s).support a
    Staked (eventK U x (Blush.fan (Q x) 0 s C a hA hX) (d:=d) (Guard.Keeper.sufficient h)) (A.B.bake.make meshT|>.rep N n m) (Doors.rate L₀*(d'/ Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))):=by
    intro y; let t:=Doors.rate L₀*(y/ Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))
    let F':= Blush.fan (Q x) 0 s C a hA hX; let p:=F'
    have hv := support_zero (S').ratio _ (show 0 ∈ F'.live.crest from hX.tagged hc); have hg:= glyphBound A.B.a (m+1)
    have hf:0≤y:= mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hA 1))
    have hw: Doors.rate L₀*y ≤ t:= mul_le_mul_of_nonneg_left (le_div_self hf hg.1 hg.2) (Doors.rate_pos _).le
    let B':=houseS U x
    have hx: ∃ s': B'.fragrances → ℝ, SumBudget (fun i=> Local.reservedMass (A.B.a.budget m) (locus F'.live B' 0 i) (s' i)) (coinFee G (X.p.profile i₀) d L₀*y) ∧ ∀ i,prince F'.live B' i→ (A.B.a.budget m).supBounds 0 (locus F'.live B' 0 i) (pane B' F' vb i) (s' i):=by
       refine ⟨(fun i=>0),?_,fun i hi=> (never B' F'.live s rfl i hi).elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) hf)
    let v:=Extra.Histories.fare (RT) s C; have hu:v=F'.milk:=Blush.rose (Q x) 0 s C a hA hX
    have hL : Fancy tu H N n m (hol G) v (Blush.scope B' F' 0) (Blush.screen B' F' (pupil U x F'.live) (pupil U x F'.pale) vb (F)) 0 (authors A.B.a m) t t:= hu.symm ▸ sendsJ g hm h hC U x he ht hp hh hd F' hv hx hw
    exact stakeDebit U x hp hd (Blush.fan ..) (Guard.Keeper.sufficient h) hL (choice.represents N n m hm.le)
end YM.PhysicalNext.Repeat.Graces

