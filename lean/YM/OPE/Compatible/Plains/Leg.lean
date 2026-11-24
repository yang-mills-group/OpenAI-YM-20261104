import YM.OPE.Compatible.Loire.Till
import YM.OPE.Compatible.Rhus.Scar
import YM.Next.MAXWELL.Core
/-!
# Leading finite scripts matched to WickPol. Weighted filters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume Flume.Script Flock StageLight Balsam Nestle Maxwell Maxwell.Free YM.Pert.Bare
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n:Side}{G:Gauge}{C:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k:ℕ}
abbrev Reed (G:Gauge):= Nestle.Pose × G.ColorIndex
abbrev rayLeg (p:Reed G):Maxwell.Probe G p.1.m.length:= ((p.1.m.length).factorial:ℝ) • Maxwell.Free.leg (fun i=>basis (p.1.m.get i)) p.2 p.1.a p.1.b
abbrev planeLeg (p:Reed G):= Maxwell.symbol _ (rayLeg p)
abbrev Ice (G:Gauge)(n:Side):=deck (Shade G) n
def fence (p:Reed G)(x:Site n):Module.Dual ℝ (Ice G n) := tip p.1 (fun a z=> LinearMap.proj (z,a,p.2)) x
lemma fee (p:Reed G)(x:Site n)(q:Ice G n): fence p x q= tip p.1 (fun i z=>q (z,i,p.2)) x:= act_tip (LinearMap.applyₗ (R:=ℝ) (M:=Ice G n) (M₂:=ℝ) q).toAddMonoidHom ..
lemma in_fields (H:Even n.val)(p:Reed G)(x:Site n)(h:Libra.Keys G (Weir.Limb H)):
   fence p x (fun w=>exclaim H h w.2.1 w.1 w.2.2)= poseT H x p.2 p.1 h :=by rw [fee]; exact (act_tip (LinearMap.applyₗ (R:=ℝ) (M₂:=ℝ) h).toAddMonoidHom (StageLight.Tags H p.2) p.1 x).symm
abbrev Marked (G:Gauge)(k:ℕ):= Axis × Axis × (Fin k→Axis) × G.ColorIndex
def fLead (p:Marked G k):Reed G:=⟨⟨List.ofFn p.2.2.1,p.1,p.2.1,0⟩,p.2.2.2⟩
lemma pLeg (p:Marked G k): (fLead p).1.heat=k+2:=by simp [fLead,Pose.heat]
abbrev θ (A:Response G k)(p:Marked G k):ℝ:= A p.1 p.2.1 p.2.2.1 p.2.2.2
lemma spheric (u:Maxwell.TaylorTower G)(p:Marked G k): Maxwell.probe u (planeLeg (fLead p))=(( ((k.factorial:ℝ) * θ (components (gaugeJet (u k))) p):ℝ):ℂ):=by
    rcases p with ⟨i,j,l,r⟩; unfold planeLeg; rw [symbol_test]; apply congr_arg; unfold rayLeg; exact measureAxis u r i j l (List.ofFn l) rfl
where
 measureAxis (u: Maxwell.TaylorTower G)(v:G.ColorIndex)(i j:Axis)(l:Fin k→Axis)(L:List Axis)(h:L=List.ofFn l):((((L.length).factorial:ℝ) • Maxwell.Free.leg (fun i=>basis (L.get i)) v i j) (u L.length))=(k.factorial:ℝ)*θ (components (gaugeJet (u k))) ⟨i,j,l,v⟩:=by
      have hp:k=L.length:=by simp [h]
      subst k; unfold θ components; rw [match_leg]; rw [LinearMap.smul_apply, leg_eval,smul_eq_mul]; have ht: L.get=l:=by funext i; simpa [List.get_eq_getElem] using congr_arg (fun L : List Axis=> L[i.val]?.getD (l i)) h
      dsimp only
      rw [ht]
lemma edgeM {E:Type*}[AddCommGroup E][Module ℝ E](l:Fin d→Axis)(y:Site n→E)(x:Site n)(z:Cover):
   trainX E d l (fun b=> y (x+Lattice.wrap n b)) z=Knot (List.ofFn l) y (x+Lattice.wrap n z):=by
      induction d generalizing y z with
      | zero=> rfl
      | succ d ih=>
        rw [trainX,LinearMap.comp_apply,show movesX E (l 0) (fun b=> y (x+Lattice.wrap n b))=(fun b=> fwd (l 0) y (x+Lattice.wrap n b)) from funext fun u=> by rw [moveX_eq, map_add,wrap_step,← add_assoc];rfl,ih,List.ofFn_succ]; exact congr_fun (Knot_f ..) _
-- value of slope
lemma enroll (A:Ice G n)(x:Site n)(p:Marked G k):
 let V(b: Cover × Shade G):= A (x+Lattice.wrap n b.1,b.2)
 slopeH G k V p.1 p.2.1 p.2.2.1 p.2.2.2= (k.factorial:ℝ)⁻¹ * fence (fLead p) x A:=by
    intro V; obtain ⟨i,j,l,r⟩:=p; let F(a:Axis)(z:Site n):G.Color:= toLp 2 (fun c=> A (z,a,c)); let y:= fwd i (F j)- fwd j (F i); have ht:curve G i j V=fun b=> y (x+Lattice.wrap n b):=by
       funext b; ext1 c; unfold V y fwd F; change ((A (x+_,j,c)-_) - (A (x+_,i,c)-_))=_; simp_rw [map_add,wrap_step,← add_assoc];rfl
    change (k.factorial:ℝ)⁻¹*chin r (trainX G.Color k l (curve G i j V) 0)= _; rw [ht,edgeM,map_zero,add_zero,fee]; congr 1; let q:= (fLead (G:=G) (k:=k) ⟨i,j,l,r⟩).1
    have he:Knot (List.ofFn l) y x=tip q F x:=by unfold tip; rw [show q.x=0 from rfl,map_zero,add_zero];rfl
    rw [he]; exact act_tip (chin r).toAddMonoidHom F q x
end YM.OPE.Prairies
