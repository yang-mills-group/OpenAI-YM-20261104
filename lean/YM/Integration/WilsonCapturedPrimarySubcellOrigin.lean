import YM.OPE.Samples.Layout

/-! One rounding cell suffices when reanchoring genuine microscopic child sites. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySubcellOrigin
open Lattice RG Wilson
variable {G:Gauge} (C:Family G) {N j per:ℕ}

theorem origin {m n:Side} (g:Ratio m n) : g.parent 0=0 :=by
  have embedded : g.embed (0:Site m)=0:=by simp [Ratio.embed]
  simpa only [embedded] using g.embed_parent (0:Site m)

theorem distance (live:j ≤ N) (x o:Site (C.side N per)) :
    let g:=C.S.toDepth live per
    separation (g.parent (x-o)) 0 < separation (g.parent x) (g.parent o)+2 :=by
  let g:=C.S.toDepth live per
  have left:=(OPE.Log.Trunk.Canvas.expands (C:=C) (x-o) 0 live).1
  have right:=(OPE.Log.Trunk.Canvas.expands (C:=C) x o live).2
  change g.count.val*separation (g.parent (x-o)) (g.parent 0) < separation (x-o) 0 + g.count.val at left
  change separation x o < g.count.val*separation (g.parent x) (g.parent o)+g.count.val at right
  rw [origin g, show separation (x-o) 0=separation x o by simp [separation]] at left
  change separation (g.parent (x-o)) 0 < separation (g.parent x) (g.parent o)+2
  have gap:g.count.val*separation (g.parent (x-o)) 0 < g.count.val*(separation (g.parent x) (g.parent o)+2) :=by
    rw [Nat.mul_add,Nat.mul_two];omega
  by_contra! wrong
  exact (not_le_of_gt gap) (Nat.mul_le_mul_left g.count.val wrong)

end YM.Integration.WilsonCapturedPrimarySubcellOrigin
