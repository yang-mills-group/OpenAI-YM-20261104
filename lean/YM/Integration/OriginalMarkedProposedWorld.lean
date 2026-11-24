import YM.Gaps1020.Local.Brace

/-! Identify the entire activity output of a physical Spring before reading
its hard activities or forced addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedProposedWorld
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat
variable {G : Gauge} {metal : Metals G} {roll : Rolls metal.p} {alloy : Alloy metal roll}
    {factory : Roost.Factor alloy} {upper stage period : ℕ} {lo hi : ℝ}
    {inlet : UVNext.CouplingReset.In alloy.B.a stage period}
    (H : Mallow.Spring factory upper stage period lo hi inlet) (x : Set.Icc lo hi) (degree : ℕ)

local notation "n₀" => alloy.B.a.S.side stage period

/-- Unfold precisely the native installation. Both sides are full Activities
on the specified physical field period. -/
theorem installed :
    @Eq (Activities G n₀)
      (GapsLocal.Renew.proposed (G:=G) (X:=metal) (D:=roll) (A:=alloy) (R:=factory)
        (N:=upper) (m:=stage) (n:=period) (l:=lo) (s:=hi) (Y:=inlet) degree H x)
      (GapsLocal.Renew.coverWorld (G:=G) (n:=n₀) (@Rep.activities G n₀ (H.result x.val))
        (Rain.opening H.H) (alloy.B.a.budget stage) (alloy.B.kin.path upper stage)
        (alloy.B.a.params stage).clip (GapsLocal.Renew.paintLow H x degree)
        (alloy.B.kin.alpha upper stage)) := by
  unfold GapsLocal.Renew.proposed
  rfl

end YM.Integration.OriginalMarkedProposedWorld

