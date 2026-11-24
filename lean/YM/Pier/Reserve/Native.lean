import YM.Pier.Reserve.Lathe
import YM.Pier.Reserve.Assembly
import YM.RG17.Witness
import YM.FullVolume.Gables.Vendee
/-!
# Producer for the actual Run's full supported single-source column reserve

Do not ask for `Blown` on some choice of transfer: this is *every actual*
`R.family.factory d N p` book for Run/Campaign/Pillars. Consequently the new
+2-exp regular reserve applies to the stronger (all flag integral) Strobe
techniques too, once the other schedule prerequisites there are supplied.

On this step to prove the regular reserve it suffices to use the convex
column bound throughout; we can afford dropping even our improvement on the
forced input. See Assembly for the version with gain & actual Span.
Adapted from FullVolume/{Mark/Sanctum,Hinge,Gables/Crown} & RG17.Columns.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pier
open Finset Function Set Filter MeasureTheory Lattice Wilson RG Source Labels Bid
  Extra.Histories Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
  MergeProof MergeProof.Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

namespace Slate
variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {H : History G} {N p j : ℕ}
    {Y : Hol G} {S: Desk G (H.S.side (j+1) p)}
local notation "Out" => H.rep N p j
local notation "Old" => H.rep N p (j+1)
local notation "L" => H.S.block j
local notation "k₀" => (kappa H j)
local notation "k₁" => Real.sqrt (H.levels.clock.forcedAllowance (j+1))
set_option quotPrecheck false
local notation "s₁" => (H.levels.params (j+1)).columns

variable (P : Tool F H N p j) {D : GaugeDoor (H.rep N p (j+1)) (H.rep N p j)}
    {W : Worth} {T : Heading F} {X : Set Wing} {u ζ v fE fK : ℝ}
    {B : SectionData F} (h : Tool.Cap P B Y W D T u ζ v X)
    (hc : Lathe H N p j Y B (H.rep N p (j+1)) P.plate D u ζ)
    (hw : Well (H.rep N p (j+1)) S (Real.sqrt (H.levels.clock.forcedAllowance (j+1))))

local notation "Wc" => u+ζ*s₁
local notation "W0" => fun x:F.Coeff=>F.coeffSize (vowel F (H.S.block j) (F.core x))
include h hc hw
lemma buffered (i:F.Index) (z : Coin F Y S)
    (hp : Tab (book (Size.axis F i) (Coin.uses z)) 0 Old (kappa H (j+1)) fE fK) :
    let x := Size.axis F i
    let A := book x (Coin.uses z)
    let m := fE + Real.sqrt (H.levels.clock.forcedAllowance (j+1))*fK
    Span B H N p j Y (P.shot i (Coin.uses z)) (A.exponentialEntry 0 B Old)
        (profile ((Old).activities) A.forced) (x 0) D X (A.density 0 B Old) (T.leads L x)
        (ζ*(F.coeffSize (F.core x)+m)) (u*W0 x+ζ*m) (v+2*m) ∧
      Room (P.shot i (Coin.uses z)) 0 Out k₀ (rotationBudget (Out).p) (u*W0 x+ζ*m) := by
    intro x A m
    exact assemble B H N p j Y P.plate P.up A X D i h.shines h.late (granted hw Y x z).1 hp rfl rfl
      h.dish h.budget.epsilon h.copies hc h.cart

lemma ledgerPortfolio (Q : Gram F Y S ((H.levels.params (j+1)).columns)) (i:Tally F) :
    Room (P.portfolio Q.scythe i) 0 Out k₀ 1 ((Wc)*W0 (Size.axis F i.2)) := by
  let x := Size.axis F i.2
  obtain ⟨a,b,hT,hB⟩:= rem_tabs.mp (granted hw Y x (Q.scythe i.2)).2
  obtain ⟨hv,hR⟩:= buffered P h hc hw i.2 _ hT
  have hS:s₁≥0:= zero_le_one.trans (H.levels.params (j+1)).columns_ge
  have ht : a+k₁*b ≤ s₁*W0 x :=
    (show a+k₁*b ≤ a+b from add_le_add le_rfl (mul_le_of_le_one_left hT.second h.hv)).trans
      (hB.trans ((Q.toll _).trans (mul_le_mul_of_nonneg_left (Work.G08.size_vowel F L _).1 hS)))
  exact (Room.auditioned i.1 (P.whirl i.1)
    ((by decide : 2 ≤ 4).trans (Next.Foundations.actual_side_ge H.S j p))
    h.good hv.earns.format hR).larger ((add_le_add_right
      (mul_le_mul_of_nonneg_left ht h.budget.epsilon) _).trans_eq (by unfold x; ring))

lemma ledgerPoint (Q : Gram F Y S ((H.levels.params (j+1)).columns)) (x : F.Coeff)
    (hp : roomCost H.levels W) (hB : Bank W H.levels) :
    Room (Q.point P x) 0 Out k₀ 1
      ((H.levels.params j).columns * F.coeffSize (F.core (Q.point P x).x)) := by
  have he := Room.combine (code _) 
      (le_refl (1:ℝ)) (Real.sqrt_pos.mpr (forcedPos ..))
      (fun i => (ledgerPortfolio P h hc hw Q i).weighted (chips F x i)) Summable.of_finite
  rw [tsum_fintype] at he
  have hf:= P.stained h hw Q.scythe (fun i=> Q.toll _) x
  exact he.larger ((residual_bill F L (Wc) (add_nonneg (zero_le_one.trans h.budget.cost)
    (mul_nonneg h.budget.epsilon (zero_le_one.trans (H.levels.params (j+1)).columns_ge))) x).trans
    (Work.G08.cone_step W H hp hB j F _ _ _ _ hf.2.2 le_rfl).1)
end Slate

end YM.Pier

namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash FullVolume
open YM.MergeProof MergeProof.Accent
open Muse Matric Pier

namespace Campaign

/-- Any actual non-bare `factory` entry of the Jewel's Run at any supported horizon has
    this simultaneous full-column reserve. No floor fixed N or eventual p premise. -/
theorem fitsPier {R:Run G} {T:Campaign R} (W:Pillars R T) (h:G.Simple)
    {m N p d : ℕ} (hm : R.family.ref d ≤ m) (he:m < N)
    (x : (R.family.labels.level d).Coeff) :
    let V := (R.family.factory d N p).entries m x
    Room V 0 (R.family.path.rep N p m)
        (Real.sqrt (R.family.path.levels.clock.forcedAllowance m)) 1
        ((R.family.path.levels.params m).columns *
           (R.family.labels.level d).coeffSize ((R.family.labels.level d).core V.x)) := by
  intro A
  let b:=R.b; let hz:=R.tuning.receipts; let V:= R.stories d N p; let U:= W.yields N p
  change (R.t d) ≤ m at hm
  have hw := W.ports d N p (hm.trans he.le)
  obtain ⟨S,hS⟩:= (show Branch.Piano R.b U (fun i=> Boutique.brochure R.T i p hz) (Nat.zero_le _)
    (R.accepts d) V (hm.trans he.le) from hw)
  let hp i:= Boutique.brochure R.T i p hz
  have hi:=R.accepts d |>.trans (R.alloy.B.a.fits.mono hm)
  let D := U.steps m (Nat.zero_le _) he
  let P := D.castT R.b U.choice hi
  obtain ⟨Y,X,hX,hY⟩:= Boutique.capTriangle h R.b D U.choice hi hz
  have hh := Boutique.pierTables h R.b D U.choice hi hz
  let hD := U.notices hp (show 0 ≤ m+1 from Nat.zero_le _) he
  have ht := U.sungAt b hp (Nat.zero_le _) (R.accepts d) (m+1) (hm.trans m.le_succ) he hS
  have hB : A = (S.tone m).plays x := by change V.entries m x = _; rw [hS.2.1]; rfl
  have hA : (S.tone m).plays x = (measure ht P.up hD).point P ((S.tone (m+1)).index x) :=
    (hS.2.2.2 m hm he).2.2 ht x
  rw [hB,hA]
  exact Pier.Slate.ledgerPoint P hX hh hD _ _ R.b.clock.room R.b.clock.bank
end Campaign
end YM.PhysicalNext.Repeat.Legato
