import YM.RG05Readout.Many.Pick
import YM.RG05Readout.Flatten.Joints

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentChart
open Function Lattice RG Extra.Histories RG05Readout RG05Readout.Many RG05Readout.Native RG05Readout.Flatten
open scoped Classical
variable {G:Gauge} {C:Family G} {b p:ℕ} {I:Type}
variable (o:I → Site (C.side b p)) (F:I → Body)
local notation "E" => (fun _:I=>(1,false) : I → Motion)
local notation "q" => (fun z:ManyStem C o b=>F z.val.1)

private theorem assemble_at {c f:Side}(d:Ratio c f)(x:Site c)(t:Site d.count):
    affine 1 (d.embed x) (d.assemble (0,t))=d.assemble (x,t):=by
  have identity:(1:Signed).act (wrap f (lift t))=wrap f (lift t):=by simp
  change (1:Signed).act (d.embed 0+wrap f (lift t))+d.embed x=d.embed x+wrap f (lift t)
  rw [show d.embed 0=0 from d.root.map_zero,zero_add,identity,add_comm]
 
/-- The physical test of a resident in the unrotated source is the same original affine test at its whole residue. -/
theorem heading {i:ℕ}(bi:b ≤ i)(z:ManyStem C o i):
    headings o E q i z=feeR (C.S.toDepth bi p) ((C.S.toDepth bi p).residue z.val.2) (F z.val.1):=by
  induction i,bi using Nat.le_induction with
  | base=>
    rw [(headlines (N:=b) o E q).1]
    let a:=C.S.toDepth (le_refl b) p
    have zero (t:Site a.count):t=0:=Fintype.card_le_one_iff.mp
      (by rw [site_card,ratio_one a,one_pow]) t 0
    rw [zero (a.residue z.val.2)]
    apply Subtype.ext
    funext y
    change (F z.val.1).val y=(F z.val.1).val (placeR a 0+((a.count.val:ℝ)⁻¹) • y)
    rw [originR,ratio_one];simp
  | succ i bi ih=>
    let a:=C.S.toDepth bi p
    let d:=(C.path.levels.clock.op i p).ratio
    let c:=C.S.toDepth (bi.trans i.le_succ) p
    let S:=Mine.tree o E
    let v:=S.narrows i bi z
    have label:z.val.1=v.1.val.1:=S.loyal i bi z
    have step:z.val.2=d.assemble (v.1.val.2,v.2):=by
      have eqn:=S.future i bi z
      change z.val.2=affine 1 (d.embed v.1.val.2) (d.assemble (0,v.2)) at eqn
      exact eqn.trans (assemble_at d v.1.val.2 v.2)
    let u:=a.residue v.1.val.2
    have nested:=chain_assembly a d c (C.S.toDepth_odd bi p) (C.S.block_odd i)
      (u,v.2) (a.parent v.1.val.2)
    have home:a.assemble (a.parent v.1.val.2,u)=v.1.val.2:=a.unpack_at _
    rw [home,←step] at nested
    have whole:c.residue z.val.2=chain a d c (u,v.2):=by rw [←nested,Ratio.assemble_res]
    have entered:headings o E q (i+1) z=headFee C p i v.2 (headings o E q i v.1):=
      (headlines (N:=i+1) o E q).2 i bi (Nat.lt_succ_self i) z
    rw [entered,ih v.1]
    change feeR d v.2 (feeR a u (F v.1.val.1))=feeR c (c.residue z.val.2) (F z.val.1)
    rw [whole,fee_chain a d c (C.S.toDepth_odd bi p) (C.S.block_odd i),label]

end YM.Integration.WilsonReportHarvestResidentChart
