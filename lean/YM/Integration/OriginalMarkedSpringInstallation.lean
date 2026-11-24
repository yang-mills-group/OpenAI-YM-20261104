import YM.Integration.OriginalMarkedRepFields
import YM.Integration.OriginalMarkedSpringHard
import YM.Gaps1020.Local.Verified

/-! Preserve all six RG fields on the actual physical presentation after
the paid whole-activity transport on the chosen Spring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedSpringInstallation
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat
open OriginalMarkedSpringHard
variable {G : Gauge}
variable {metal : Metals G} {roll : Rolls metal.p} {alloy : Alloy metal roll}
    {factory : Roost.Factor alloy} {upper stage period : ℕ} {lo hi : ℝ}
    {inlet : UVNext.CouplingReset.In alloy.B.a stage period}
    (H : Mallow.Spring factory upper stage period lo hi inlet) (x : Set.Icc lo hi) (degree : ℕ)
local notation "n₀" => alloy.B.a.S.side stage period
local notation "made" => GapsLocal.Renew.proposed (G:=G) (X:=metal) (D:=roll) (A:=alloy) (R:=factory)
    (N:=upper) (m:=stage) (n:=period) (l:=lo) (s:=hi) (Y:=inlet) degree H x
local notation "base" => @Rep.activities G n₀ (H.result x.val)

theorem presentation :
    OriginalMarkedRepFields.Fields (G:=G) (n:=n₀) (GapsLocal.Renew.presentation degree H x)
      (H.result x.val) := by
  let B : Rep G n₀ := H.result x.val
  let P : Activities G n₀ := (made)
  have h : HardFields P B.activities := hard H x degree
  unfold GapsLocal.Renew.presentation
  exact OriginalMarkedRepFields.replace B P h.forced h.charges

end YM.Integration.OriginalMarkedSpringInstallation
