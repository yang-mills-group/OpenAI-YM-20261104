import YM.FVAAlt2.Winder.Pivot
import YM.RegulatorIR.Diagram.Heat
/-! # Even loop invariants under centered L¹ lift. Path lengths not paid through loop example mark. For every fixed topology of vacuum union. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget.FVAAlt2.Wind
open Set Filter Function Tuple Packet Layer
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X Y Z W : Type} {l:Filter W} {K:Layer X X} {U:W→Layer X X} {C D : ℝ≥0∞} {i j r s:ℕ}
section Loops
variable {v: Packet X (r+2)} {F: W→Packet X (r+2)}
lemma transit {Z:Type}{v:Z× (X×X)→ℝ}{F:W→ Z×(X×X)→ℝ} (m:Earn l C v F)(n:SplitT l D K U): Earn l (C*D) (fun x=> ∑'y:X×X,K y.1 y.2*v (x,y)) (fun w x=>∑'y:X×X,U w y.1 y.2*F w (x,y)) := by
 let k (K:Layer X X)(z:Z× (X×X)):= K z.2.1 z.2.2
 have H: Earn l (C*D) (v*(k K)) (fun w=> F w*k (U w)):= m.propel n.high (fun x=> (n.earns _).point x.2.2) (fun i=> (step_through i.2.2 (K i.2.1)).trans (n.earns i.2.1).roof) (fun w i=> (step_through i.2.2 (U w i.2.1)).trans ((n.earns i.2.1).terms w))
 simp_rw [mul_comm (K _ _),mul_comm (U _ _ _)]; exact H.sumSecond
lemma Earn.loops (m:Earn l C v F)(n:SplitT l D K U): Earn l (C*D) (loop v K) (fun i=> loop (F i) (U i)):= transit (m.pays (linkEquiv _ _) (linkEquiv _ _).injective) n
lemma Pivot.loops (m:Pivot l C v F)(n:SplitT l D K U): Pivot l (C*D) (loop v K) (fun i=> loop (F i) (U i)):= ⟨ENNReal.mul_ne_top m.high n.high,fun x i=> transit ( (m.earns x i.succ.succ).pays (linkHold i x) (linkHold i x).injective ) n ⟩
end Loops
section Splice
variable {v:Packet X (r+1)}{F:W→Packet X (r+1)}{u:Packet X (s+1)}{G:W→Packet X (s+1)}
-- reassociate. avoid E defs private? custom easy
noncomputable abbrev eT : ( Z×Y )× X≃ ( X×Z )× Y:=((Equiv.prodComm (Z× Y) X).trans ((Equiv.prodAssoc X Z Y).symm))
lemma via {Z:Type} {v:X×Z → ℝ}{F:W→X×Z→ℝ}(m:Earn l C v F)(n:Pivot l D u G): Earn l (C*D) (fun z:Z× Tuple X s=> ∑'y,v (y,z.1)*u (Fin.cons y z.2)) (fun w z=> ∑'y,F w (y,z.1)*G w (Fin.cons y z.2)):= by
 have hp(y:X):= (n.earns y 0).pays _ ( Tuple.still (s:=s) y ).injective
 let f(z:X× Z)(a:Tuple X s):=u (Fin.cons z.1 a); let l'(w:W) (z:X×Z)(a:Tuple X s):= G w ( Fin.cons z.1 a )
 exact ((m.link (t:=f) (a:=l') ( fun x=> hp x.1 ) n.high).pays _ eT.injective).sumSecond
lemma pick {v':Tuple X r× Tuple X s→ℝ}{G':W→Tuple X r× Tuple X s→ℝ}(m: Earn l C v' G'): Earn l C (fun z:Tuple X (r+s)=> v' (cutLeft z,cutRight z)) (fun w z=> G' w (cutLeft z,cutRight z)):= m.pays (Fin.appendEquiv ..).symm (Fin.appendEquiv ..).symm.injective
lemma Earn.splicing (m:Earn l C v F)(n:Pivot l D u G): Earn l (C*D) (splice v u) (fun i=>splice (F i) (G i)):= pick ( via (m.pays (glueEquiv ..) (glueEquiv ..).injective ) n )
lemma Pivot.left (m: Pivot l C v F)(n:Pivot l D u G)(x:X)(i:Fin r): Earn l (C*D) (fun z:Hold (Fin.castAdd s i) x=> splice v u z.val) (fun w z=> splice (F w) (G w) z.val):=by
 let E:= Tuple.underL i x; let R:= ( Tuple.overL (s:=s) i x ).symm
 exact (via ((m.earns x i.succ).pays E E.injective) n).pays R R.injective
lemma Pivot.splicing (m: Pivot l C v F)(n:Pivot l D u G): Pivot l (C*D) (splice v u) (fun i=>splice (F i) (G i)):=by
 refine ⟨ ENNReal.mul_ne_top m.high n.high, fun x i=> Fin.addCases ?_ ?_ i ⟩
 · exact fun i=> m.left n x i
 intro i
 let E:= (((overR (r:=r) i x).symm.trans (Equiv.prodComm _ _)).trans (overL (s:=r) i x))
 have h (z: Hold (Fin.natAdd r i) x) (v:Packet X (r+1))(u:Packet X (s+1)): splice v u z.val=splice u v ( E z ).val:=by
    obtain ⟨ ⟨a,b⟩,rfl ⟩ := (overR i x).surjective z; unfold E; simp only [Equiv.trans_apply,Equiv.symm_apply_apply]; exact twist ..
 simp_rw [h]; rw [mul_comm]; exact (n.left m x i).pays E E.injective
variable {R:ℝ≥0∞}
lemma Pivot.knots (m: Pivot l C v F)(n:Pivot l D u G)(hp:SplitT l R K U) : Pivot l (C*(D*R)) (knot K v u) (fun i=> knot (U i) (F i) (G i)):= m.splicing (n.rays hp 0)
lemma Earn.knots (m: Earn l C v F)(n:Pivot l D u G)(hp:SplitT l R K U) : Earn l (C*(D*R)) (knot K v u) (fun i=> knot (U i) (F i) (G i)):= m.splicing (n.rays hp 0)
end Splice
end YM.RegulatorIR.Budget.FVAAlt2.Wind
