import YM.OPE.Compatible.Gully.Will
import YM.OPE.Compatible.Chain.Badges
/-!
# Footprints on the boost chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.StageLight
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch Further.FreeCovariance.KP MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Nestle Balsam Weir
open GaussianScore Libra
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n m:Side}{G:Gauge}{C:RG.KernelChoices}{r:ℕ}
variable {V:Type*}[AddCommGroup V]
lemma Knot_sum {I:Type*}(l:List Axis)(x:Finset I)(f:I→Site n→V)(z:Site n):Knot l (fun y=>∑ i∈x,f i y) z=∑ i∈x,Knot l (f i) z:=by
    induction l generalizing z with
    | nil=>rfl
    | cons a l ih=> change Knot l _ _-Knot l _ _= _; rw [ih,ih]; rw [← Finset.sum_sub_distrib];rfl
lemma cork_sub (l:List Axis)(f g: Site n→V)(x:Site n): Knot l (f-g) x=Knot l f x-Knot l g x:=by
   induction l generalizing x with
   | nil=>rfl
   | cons a l ih=>change Knot l (f-g) (x+_)- Knot l (f-g) x= (Knot l f _-Knot l f x)-(Knot l g _-Knot l g x); rw [ih,ih]; abel
lemma zeroKn (l:List Axis):Knot (n:=n) l (0:Site n→V)=0:= by
   induction l with | nil=> rfl | cons i l ih=>change fwd i (Knot l (0:Site n→V))=0;rw [ih]; ext p;simp [fwd]
lemma fwd_back (p t:Axis)(f:Site n→V):fwd p (fwd t f)=fwd t (fwd p f):=by funext x; unfold fwd;rw [add_right_comm x];abel
lemma Knot_f (l:List Axis)(f:Site n→V)(i:Axis):Knot l (fwd i f)=Knot (i::l) f:=by
   induction l with
   | nil=>rfl
   | cons a l ih=> change fwd a (Knot l (fwd i f))= fwd i (fwd a (Knot l f)); rw [ih]; exact fwd_back _ _ _
lemma tip_sum {I:Type*}(p:Pose)(x:Finset I)(v:I → Axis→Site n→V)(z:Site n):tip p (fun i b=>∑ j∈x, v j i b) z =∑ i∈x, tip p (v i) z:=by
   unfold tip; rw [show (fwd p.a _-fwd p.b _)=(fun y=>∑ j∈x,(fwd p.a (v j p.b)-fwd p.b (v j p.a)) y) from ?_]; exact Knot_sum ..
   funext y; simp_rw [Pi.sub_apply]; simp only [fwd]; rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
lemma act_kn {W:Type*}[AddCommGroup W](A:V→+W)(g:Site n→V)(l:List Axis)(x:Site n):A (Knot l g x)=Knot l (A ∘ g) x:=by induction l generalizing x with | nil=>rfl | cons a l ih=> change A (Knot l _ _-Knot l _ _) = Knot l _ _-Knot l _ _; rw [map_sub,ih,ih]
lemma act_tip {W:Type*}[AddCommGroup W](A:V→+W)(v:Axis→Site n→V)(p:Pose)(k:Site n): A (tip p v k)=tip p (fun j i=>A (v j i)) k:=by
    unfold tip; rw [act_kn A]; apply congr_fun; congr 1; ext1 x; simp only [fwd,Function.comp_apply, Pi.sub_apply,map_sub]
variable (H:Even n.val)
local notation "X!"=>Keys G (Limb H)
abbrev Tags (a:G.ColorIndex)(i:Axis)(x:Site n):=MarkC H a (addressR (x,i))
abbrev poseT (x:Site n)(a:G.ColorIndex)(p:Pose): Module.Dual ℝ X! := tip p (Tags H a) x
omit H
lemma tipPapers (p:Pose)(x y:Site n)(a:Axis): tip p (fun i z=> if i=a then mildX [] (z-y) else 0) x= paper p a x y:=by
     let f(z:Site n):= mildX [] (z-y); let l:= p.m; let t:= x+wrap _ p.x; have ht(l:List Axis)(z:Site n):Knot l f z=mildX l (z-y):=by
         induction l generalizing z with
         | nil=> rfl
         | cons i l ih=>change Knot l f (z+step i)-Knot l f z=_; rw [ih,ih,mild_more]; rw [sub_add_eq_add_sub]
     unfold paper Pose.Lck tip; dsimp only;rw [cork_sub, Knot_f,Knot_f, sub_add_eq_add_sub]
     have hp (i b l):Knot (n:=n) l (fun z=>if i=a then mildX [] (z-y) else 0) b=if a=i then mildX l (b-y) else 0:=by
         split_ifs with h h' h'; · exact (show Knot l _ _=_ from ht _ _)
         · exact False.elim (h' h.symm)
         · exact False.elim (h h'.symm)
         · exact congrFun (zeroKn (n:=n) (V:=ℝ) l) _
     rw [hp,hp]
-- wick
include H
lemma wickPose (x y:Site n)(a:Axis)(p:Pose)(i j:G.ColorIndex)(h:4≤ r):
  Tags H j a y ((boost H (Train.top r) h C).inverse (poseT H x i p)) =if i=j then ∑ k:Kv, torque p k*paper (reed p k) a (decks k x) y else 0:=by
    let M:= boost H (Train.top r) h C (G:=G); let Y:=M.inverse (Tags H j a y); have hp:(M.P (M.inverse (poseT H x i p))) Y=(Tags H j a y) (M.inverse (poseT H x i p)):= by rw [M.turns, show M.P Y= _ from M.applies _]
    rw [show Tags H j a y ((boost H (Train.top r) h C).inverse (poseT H x i p))= poseT H x i p Y from hp.symm.trans (congrArg (· Y) (M.applies ..))]
    let A:Module.Dual ℝ X! →ₗ[ℝ]ℝ:= {toFun φ:= φ Y, map_add':=fun _ _ =>rfl,map_smul':=fun _ _=>rfl}
    rw [show poseT H x i p Y=tip p (fun b z=> A (Tags H i b z)) x from act_tip A.toAddMonoidHom _ _ _]
    let U(b:Axis)(z: Site n):= if b=a then mildX [] (z-y) else 0
    have hv(b:Axis)(z: Site n): A (Tags H i b z)=(if i=j then ∑ k:Kv,omegaK k b * U b (ferry k (z,b)).1 else 0):=by
         rw [show A _= M.wick (Tags H j a y) (Tags H i b z) from rfl]; change boostJet H h _ _ j i _ _=_; rw [pages]; split
         · apply Finset.sum_congr rfl; intro k _; rw [Terp.letter,ferry_at]; change (if (axisK k).flip b then -lineC _ _ (_,coord b) (_,coord a) else lineC _ _ (_,coord b) (_,coord a))=_; unfold U omegaK; by_cases hp:b=a <;> split_ifs <;> first|simp [strip_field (C:=C) h,coord_iff,hp]
         rfl
    split
    next hh=>simp_rw [hv,if_pos hh]; rw [tip_sum p (I:=Kv) (v:=fun k i z=>omegaK k i * U i (ferry k (z,i)).1)]; refine Finset.sum_congr rfl (fun k _=>?_); exact (torn U k p x).trans (congrArg (torque p k • ·) (show tip _ U _ = _ from tipPapers (reed p k) (decks k x) y a))
    next hh=> simp_rw [hv,if_neg hh]; change tip p (fun _ _=>0) x=0; unfold tip; have h(i) :fwd i (0:Site n→ℝ)=0:= funext fun _=>sub_self _; change Knot p.m (fwd p.a 0 - fwd p.b 0) _=0; rw [h,h,zero_sub_zero,zeroKn];rfl
end YM.OPE.StageLight
