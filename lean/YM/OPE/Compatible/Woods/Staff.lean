import YM.OPE.Compatible.Woods.Moss
import YM.Push.FREE_RESOLVENT.Flat
/-!
# Residue standing order gives a single alphabet for all steps
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Lattice Laurent Tree Function Filter Finset Wilson RG Bloch Exterior FreeResolvent
open scoped Topology BigOperators ComplexConjugate
variable {L c f: Side}
def staffs (L:Side) (v: Edge (Site L)): Prop := ∃ i: Site L,i ≠ 0 ∧ (riseA i).used i=v
-- canonical decidable
instance (L:Side): DecidablePred (staffs L) := by intro i; unfold staffs; infer_instance
variable (g:Ratio c f) (hp:Odd g.count.val)
lemma same_use (d:Step)(x:Site f): (g.residue (d.used x).1,(d.used x).2)=d.used (g.residue x):=by
   cases h:d.neg
   · simp [Step.used,h]
   simp only [Step.used,h,if_true,map_sub,Prod.mk.injEq, and_true]
   rw [← wrap_step f, Ratio.residue_wrap, wrap_step]
lemma used_injective (d:Step): Injective fun x:Site g.count=> d.used x:=by intro i j; cases h:d.neg <;> simp [Step.used,h]
lemma same_stand (d:Step): Surjective (fun i:Site f=>(d.used i).1):=by
   intro i; cases h:d.neg
   · exact ⟨i,by simp [Step.used,h]⟩
   exact ⟨i+step d.dir, by simp [Step.used,h]⟩
lemma staff_trunk (x:Edge (Site f)): x ∈ (forest g hp).trunks ↔ staffs g.count (g.residue x.1,x.2):=by
   rw [Forest.trunk_mem_iff]; constructor
   · rintro ⟨i,hi,e⟩; rw [← e]; exact ⟨g.residue i,(leaves g _).mp hi,(same_use g _ _).symm⟩
   rintro ⟨i,hi,hx⟩
   obtain ⟨v,hv⟩:= same_stand (riseA i) x.1
   have ha(R : Type) [AddCommGroup R][One R] (u:Four R): ((riseA i).used u).2=(riseA i).dir := by simp only [Step.used]; split <;> rfl
   have hh:(riseA i).dir=x.2:= by rw [← ha _ i,hx]
   have he : (riseA i).used v=x:=Prod.ext hv (hh ▸ ha _ v)
   have ht : i=g.residue v:= used_injective g (riseA i) (by dsimp only; rw [hx, ← same_use,he])
   refine ⟨v, (leaves g _).mpr (ht ▸ hi),?_⟩;change (riseA (g.residue v)).used v=x; rw [← ht,he]
abbrev Slip (G: Gauge)(L: Side):= {x: Edge (Site L) // ¬ staffs L x} × G.ColorIndex
variable {G: Gauge}
def enlist (p:Slip G g.count): Co g.count (PAC G 1):=(p.1.val.1, coord p.1.val.2, p.2)
def squad (G : Gauge): Active G (forest g hp) ≃ Co c (Slip G g.count) where
  toFun p :=(g.parent p.1.val.1,⟨(g.residue p.1.val.1,p.1.val.2), mt (staff_trunk g hp _).mpr p.1.property⟩,p.2)
  invFun q := (⟨(g.assemble (q.1,q.2.1.val.1),q.2.1.val.2),by
     rw [staff_trunk]; simp only [Ratio.assemble_res,Prod.mk.eta]; exact q.2.1.property⟩,q.2.2)
  left_inv := by
     rintro ⟨⟨⟨x,a⟩,h⟩,i⟩; simp only [Prod.mk.injEq,and_true,Subtype.mk.injEq]; exact g.unpack_at x
  right_inv := by intro q; rcases q with ⟨x,⟨p,h⟩,i⟩; simp
lemma rooting (p:Active G (forest g hp)): (let q:= (squad g hp _ p); (q.1,enlist g q.2))=splitCo g _ (plant _ p):=by rw [split_co]; rfl
end YM.OPE.Woody
