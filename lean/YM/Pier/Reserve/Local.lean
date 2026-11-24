import YM.FullVolume.Panel.Beam
import YM.RG17.Heading
import YM.Pier.Reserve.Menu
/-! Local reserve producer, using the exact Fancy kernels on the
same `Boutique.stock`. On forced input, in particular, *don't weaken*
when pricing the bill -- there is no prince to pay. The hit estimate
with no input-divisor already covers the full output, including *its*
forced divisor (different level), and true push/transfer on the current
history. From that one obtains a genuine small-coupling estimate on the
forced-input part of the mark response, not just on coefficients.
Derived from Panel/{Heaven,Uprise,Port,Beam} and RG17/Heading.
-/
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

open Pier Matric
omit hC g hh he ht h
/-- Both Tab (at the right actual divisor) and enhanced regular reserve under a common charge. -/
lemma turnPier (T' : Cloud (Q x))
    (K' : Guard.Keeper ((O).p) ((O).activities))
    {f : Config G (A.B.a.S.side (m+1) n) → ℂ} {v₀ : (F).Coeff} {t r' : ℝ}
    (hF : Fancy (localSection G d) H N n m (hol G) f
      (Blush.scope (houseS U x) T' 0)
      (Blush.screen (houseS U x) T' (pupil U x T'.live) (pupil U x T'.pale) vb F)
      v₀ (authors A.B.a m) t r') :
    let V₀ := eventK U x T' (d:=d) K'
    V₀.Format 0 (hol G) O ∧
      Pier.Room V₀ 0 O (Local.kappa H m) (rotationBudget ((O).p)) r' := by
  intro V₀
  have hx := choice.represents N n m hm.le
  have hκ : 0 < Local.kappa H m := Real.sqrt_pos.mpr (forcedPos ..)
  have hr : Local.Readable (hol G) (localSection G d) (O).p
      (A.B.a.S.side m n) (authors A.B.a m) :=
    (hx.vac.symm ▸ (livelyCard hp hd (n:=n)) : Local.Readable _ _ _ _ _)
  obtain ⟨a,b,c,⟨h₁,-⟩,-,hT,⟨pQ,q,hq,h₃⟩,hA,-⟩:= hF
  exact ⟨Guard.usage _ h₁ hx.good hr,
    a,b+c,Guard.tab_mint _ h₁ hx.good hκ hr hT,h₃ ▸ Blown.deck _ h₁ hr hq,hA⟩

include hC g hh he ht h

lemma heavyPier (V:Wing→Prop) (s:ℕ) (C:Config G (A.B.a.S.side (m+1) n)→ℂ)(a:ℝ) (ha:V (.gasKey s))(hc:C≠0) (hX:SlotFit (Q x) 0 s C)(hA:∀ t,‖C t‖≤a): let d':= (RT).p.mass ((RT).activities.forced s).support a
    let t:= Doors.rate L₀ * d'
    MergeProof.Matric.Span tu H N n m (hol G) (eventK U x (Blush.fan (Q x) 0 s C a hA hX) (d:=d) (Guard.Keeper.sufficient h)) 0 (exactGas (RT).activities s C) 0 q1 V (Extra.Histories.fare (RT) s C) 0 t t (2*d') ∧
    Pier.Room (eventK U x (Blush.fan (Q x) 0 s C a hA hX) (d:=d) (Guard.Keeper.sufficient h))
      0 O (Local.kappa H m) (Pier.rotationBudget ((O).p)) t :=by
   intro y t; let F':= Blush.fan (Q x) 0 s C a hA hX; let p:=F'
   have hv := support_zero (S').ratio _ (show 0 ∈ F'.live.crest from hX.tagged hc)
   have hf:0≤y:= mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans (hA 1))
   have hw: Doors.rate L₀*y ≤ t:= le_rfl
   let B':=houseS U x
   have hx: ∃ s': B'.fragrances → ℝ, SumBudget (fun i=> Local.reservedMass (A.B.a.budget m) (locus F'.live B' 0 i) (s' i)) (coinFee G (X.p.profile i₀) d L₀*y) ∧ ∀ i,prince F'.live B' i→ (A.B.a.budget m).supBounds 0 (locus F'.live B' 0 i) (pane B' F' vb i) (s' i):=by
      refine ⟨(fun i=>0),?_,fun i hi=> (never B' F'.live s rfl i hi).elim⟩; simp only [Local.reservedMass,mul_zero]; exact Local.sumBudget_zero (mul_nonneg (coin_pos ..|>.le) hf)
   let v:=Extra.Histories.fare (RT) s C; have hu:v=F'.milk:=Blush.rose (Q x) 0 s C a hA hX
   have hL : Fancy tu H N n m (hol G) v (Blush.scope B' F' 0) (Blush.screen B' F' (pupil U x F'.live) (pupil U x F'.pale) vb (F)) 0 (authors A.B.a m) t t:= hu.symm ▸ sendsJ g hm h hC U x he ht hp hh hd F' hv hx hw
   refine ⟨?_,(turnPier hm choice U x hp hd _ _ hL).2⟩
   apply thunderJ g hm choice hC U x he ht hp hd p (Guard.Keeper.sufficient h) V (show V (.gasKey s) from ha) (hX.tagged hc) v 0 (exactGas (RT).activities s C) t t 0 ?_ ?_ hL
   · funext T;change 0=(0:ℂ)+Complex.I*0; simp
   funext z T; let b:=barcode (RT).activities s
   by_cases he:z=b
   · subst z; change (Pi.single b C : Box (A.B.a.S.side (m+1) n) → Config G (A.B.a.S.side (m+1) n) → ℂ) b T= _; rw [Pi.single_eq_same]; unfold entry; rw [show p.live.turn = .gasKey s from rfl, show p.pale.turn = .gasKey s from rfl]; change C T=(if barcode (Q x|>.activities) s=b then _ else (0:ℂ))+Complex.I*(if barcode (Q x|>.activities) s=b then _ else 0); simp only [b, if_true]; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
   unfold entry; rw [show p.live.turn = .gasKey s from rfl, show p.pale.turn = .gasKey s from rfl, exactGas, Pi.single_eq_of_ne he]; dsimp only [b] at he; simp [Ne.symm he] -- simp b def
end YM.PhysicalNext.Repeat.Graces
