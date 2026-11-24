import YM.Integration.OriginalMarkedWorldFields
import YM.Integration.OriginalMarkedProposedWorld

/-! The forced supports and genuine hard charges of the specified physical
Spring, via transport across the entire previously identified activity field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedSpringHard
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat
open Precision AnalyticBridge VerifiedReset Collection
variable {G : Gauge} {n : Side}

structure HardFields (kept current : Activities G n) : Prop where
  forced : kept.forced=current.forced
  charges : kept.K=current.K

theorem transport {P Q A : Activities G n} (e : P=Q) (h : HardFields Q A) : HardFields P A :=
  Eq.mpr (congrArg (fun B : Activities G n => HardFields B A) e) h

theorem covered (A : Activities G n) (X : Listing G n) (p : BudgetPoint) (Y : PathData G)
    (c : Clip) (J : Collection.Source G n) (a : ℝ) :
    HardFields (GapsLocal.Renew.coverWorld A X p Y c J a) A :=
  ⟨OriginalMarkedWorldFields.forced A X p Y c J a,OriginalMarkedWorldFields.charges A X p Y c J a⟩

variable {metal : Metals G} {roll : Rolls metal.p} {alloy : Alloy metal roll}
    {factory : Roost.Factor alloy} {upper stage period : ℕ} {lo hi : ℝ}
    {inlet : UVNext.CouplingReset.In alloy.B.a stage period}
    (H : Mallow.Spring factory upper stage period lo hi inlet) (x : Set.Icc lo hi) (degree : ℕ)
local notation "n₀" => alloy.B.a.S.side stage period
local notation "made" => GapsLocal.Renew.proposed (G:=G) (X:=metal) (D:=roll) (A:=alloy) (R:=factory)
    (N:=upper) (m:=stage) (n:=period) (l:=lo) (s:=hi) (Y:=inlet) degree H x
local notation "base" => @Rep.activities G n₀ (H.result x.val)

/-- The full native installation, before projecting anything out of the Spring. -/
theorem hard : HardFields (G:=G) (n:=n₀) (made) (base) :=
  transport (OriginalMarkedProposedWorld.installed H x degree)
    (covered (base) (Rain.opening H.H) (alloy.B.a.budget stage) (alloy.B.kin.path upper stage)
      (alloy.B.a.params stage).clip (GapsLocal.Renew.paintLow H x degree) (alloy.B.kin.alpha upper stage))

theorem forced : @Activities.forced G n₀ (made)=@Activities.forced G n₀ (base) :=
  (hard H x degree).forced

theorem charges : @Activities.K G n₀ (made)=@Activities.K G n₀ (base) :=
  (hard H x degree).charges

end YM.Integration.OriginalMarkedSpringHard
