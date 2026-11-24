import YangMills.WilsonProof.NativeSupport.YM.MS.Heat.Health
/-!
# Keeping all mixed momentum/time derivatives

Needed for one-loop spacetime PDE. Derivative at any given length with any
 labelled F and an independently knowable derivative F'. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Heat
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Book Convolve Base
open Wire
open scoped Topology ContDiff
variable {E E' P A I:Type}[NormedAddCommGroup P][NormedSpace ℝ P][NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup E'][NormedSpace ℝ E'][Fintype A]
variable {F H : BF A P}{K:ℝ→ Flux A P ℂ}{p: Sector A}
variable {V U: tagSmooth E A P}
omit [Fintype A][NormedSpace ℝ P] [NormedAddCommGroup P][NormedAddCommGroup E][NormedSpace ℝ E] in
lemma walk_pitch (x:E) : degree (field p) (walk0 V x)= degree (field p) V:= by induction V with| nil=>rfl| cons i l ih=> simp only [walk0,List.map_cons,degree_cons]; congr! 1
omit [Fintype A] in
lemma round_scat (p:Sector A)(w:List A)(F:E→Shared A ℂ)(h:∀ i j, Split i j w → ContDiff ℝ ∞ fun p=>F p i j): ContDiff ℝ ∞ (fun x=> scatter p w (F x)):= by induction w generalizing F with| nil=>exact h _ _ .nil | cons i w ih=> exact ih _ (fun i j hi=>(h _ _ hi.left).add (contDiff_const.mul (h _ _ hi.right))) -- remove {U}
-- gather walk0 (arbitrary smooth) map. generalized ∀ x.
omit [NormedSpace ℝ P][NormedAddCommGroup P] [NormedAddCommGroup E][NormedSpace ℝ E][Fintype A] in
lemma wander (l:tagSmooth E A P)(x:E)(p:Sector A) (F:Shared (Mode A P) ℂ) : scatter (field p) (walk0 l x) F=scatter (field p) l (fun i j=> F (walk0 i x) (walk0 j x)):= by induction l generalizing F with | nil=>rfl| cons a l ih=> rw [show walk0 (a::l) x= _ :: walk0 l x from rfl, scatter_cons, ih,scatter_cons]; congr! 3; rw [walk_pitch]; rfl
omit [Fintype A] in
lemma radius1 (q:E→ℝ)(he:ContDiff ℝ ∞ q)(hK:flex K)(i j:A)(hf:TouchF F)(h:TouchF H)(hw: Trail V)(hU: Trail U): ContDiff ℝ ∞ fun p' => radius p (K (q p')) i j (F (q p')) (H (q p')) (walk0 V p') (walk0 U p'):= by
   unfold radius; simp_rw [walk_pitch];
   let N p':= -(net (walk0 V p')); let Z:A × (E→P):= (i,N); have hN: ContDiff ℝ ∞ N:= hw.net0.neg;
   have ht := hf E q (Z::V) (hw.cons _ _ hN) he; have hx := h E q ((j,- N)::U) (hU.cons _ _ hN.neg) he; exact (((contDiff_const.mul ((hK i j).comp (he.prodMk hN))).mul (contDiff_const.mul ht)).mul hx)
lemma tree_touch (hZ:∀ i, Reverse (K i) p)(h: flex K)(ht:TouchF F)(hk:TouchF H): TouchF (fun x=>tree p (K x) (F x) (H x)):= by
   intro E _ _ f w hw he; unfold tree; simp_rw [wander]; refine round_scat _ _ _ (fun a b hh=>?_); simp_rw [convertR (hZ _)]; exact ContDiff.sum (fun i _=> ContDiff.sum fun j _=> radius1 f he h i j ht hk (hw.splitL hh) (hw.splitR hh))
-- for Q raise on all moments, contour. Need smooth `send wave`. 
lemma charge_touch (Q:Charge p P ℂ)(hh:∀ i j,ContDiff ℝ ∞ (Q.table i j))(h:TouchF F): TouchF (fun x=> Q.raise (F x)) := by
    intro E _ _ f w hw he; simp_rw [visit_Z];
    let R (x:E)(l:tagSmooth E A P)(i:A×(E→P))(r:tagSmooth E A P): ℂ:= ∑ j:A,Q.table i.1 j (i.2 x)*F (f x) (walk0 l x++(j,i.2 x)::walk0 r x)
    have ht x : (visit true p (walk0 w x) (fun l i r => ∑ j:A, Q.table i.1 j i.2 * F (f x) (l++(j,i.2)::r))) = visit true p w (R x):= by rw [walk0,Charge.mark_visit true p (z:=fun i:(A×(E→P))=> (i.1,i.2 x)) (hz:=fun _=>rfl)]; rfl
    simp_rw [ht];
    refine visit_diff (V:= R) ?_; intro a i r hx;
    have hh' : Trail (a++i::r):= hx ▸ hw; have Hx : ContDiff ℝ ∞ i.2:= hh' i (by simp);
    unfold R; refine ContDiff.sum (fun j _=> ((hh i.1 j).comp Hx).mul ?_); have hv : Trail (a++(j,i.2)::r):= by intro v h; obtain hh0|h'|h'' := List.mem_append.mp h |>.elim Or.inl (fun h=> Or.inr (List.mem_cons.mp h)); exact hh' v (by simp [hh0]); exact h' ▸ Hx; exact hh' v (by simp [h'']);
    convert! h E f (a++(j,i.2)::r) hv he using 1; ext; simp [walk0]
end YM.MS.Heat
