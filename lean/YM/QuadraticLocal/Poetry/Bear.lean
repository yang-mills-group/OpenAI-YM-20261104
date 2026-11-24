import YM.QuadraticLocal.Poetry.Rect
import YM.QuadraticLocal.Poetry.Vernal
import YM.Next.STATIONARY.Level.SliceGate
/-!
# Ever on any extent. Cover abelian gauge station for PAINTED first grade.
 Ph. archive.I.B. Several bookkeeping proofs here adapted from `RG02.Pinned.Loops,Fields`. New target
 is OUR workspace object with full L-regulator Card.P.S.Point & all costs at once, not RG02 prescription.
 This file in minimal checked closure. Ordinary curl path material, at all sides even short.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Pinned
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Push Push.Loops Stationary
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{k d : ℕ}{m:Side}{n:ℕ→Side}{a C : ℝ}
abbrev LinesC (G:Gauge):= Edge Cover → G.Color
variable (Y: LinesC G)
lemma along_price (p:Cover)(l:Walk)(h:∀ i,‖Y i‖≤a): ‖linkSum Y p l‖ ≤ a*l.length:= by
 induction l generalizing p with
 | nil=> simp [linkSum]
 | cons i b hv=> rw [linkSum,List.length_cons]; push_cast; rw [mul_add,mul_one,add_comm _ a]; refine (norm_add_le ..).trans (add_le_add ?_ (hv _)); split <;> first| (rw [norm_neg]; exact h _) | exact h _
abbrev grad (a : Cover→ G.Color) : LinesC G := fun i=> a (i.1+step i.2)-a i.1
def pathGradient (x:Cover):=linkSum Y 0 (stride_ x)
lemma path_price (p:Cover)(h:∀ i, ‖Y i‖ ≤ a) : ‖pathGradient Y p‖ ≤ a*size p:= (along_price Y _ _ h).trans_eq (by rw [show (stride_ p).length=size p from (Extra.Iteration.route_length ..).trans (by rw [sub_zero])])
private lemma era (p:Edge Cover) : (Y-grad (pathGradient Y)) p= Pinned.lead Y p.1 p.2:=by
   rw [lead,along_walk]; simp [pathGradient, Pinned.grad,linkSum,Step.used,posDir,stride_,route_end]; abel
variable (G)
def selection (p:Edge Cover):List Plaq:= (rectangles (A:=G.Color) p.1 p.2).choose
abbrev BooksC (p:Edge Cover) := Fin (selection G p).length
abbrev cite (p:Edge Cover)(i: BooksC G p):= (selection G p).get i
lemma native_count (p:Edge Cover) : Fintype.card (BooksC G p) ≤ size p.1:= (Fintype.card_fin _).le.trans (rectangles (A:=G.Color) _ _).choose_spec.1
lemma native_zone (p:Edge Cover)(i:BooksC G p): size (cite G p i).start ≤ size p.1:= (rectangles (A:=G.Color) _ _).choose_spec.2.1 _ (List.get_mem _ _)
variable {G}
lemma funded_area (p:Edge Cover): (Y-grad (pathGradient Y)) p = ∑ i:BooksC G p, Pinned.read Y (cite G p i):=by
   rw [Pinned.era, (rectangles p.1 p.2).choose_spec.2.2 Y]; let Z:= selection G p
   change List.sum (Z.map (Pinned.read Y))=∑ i:Fin Z.length, Pinned.read Y (Z.get i)
   conv_lhs=> rw [← List.ofFn_get Z]
   rw [List.map_ofFn,List.sum_ofFn]; rfl

variable (x: Site m) (A : Link G m)
def sendLink : LinesC G:= fun i=> arm G m 1 A (x+wrap m i.1,Exterior.coord i.2)
lemma orient_wrap (p:Cover)(l: Walk) : linkSum (sendLink x A) p l=linkSum (collect G (arm G m 1 A)) (x+wrap m p) l:=by
   induction l generalizing p with
   | nil=> simp [linkSum]
   | cons i l ih=>
                   rw [linkSum,linkSum,ih]; congr 1
                   · cases i with
                     | mk a b=> cases b; rfl; dsimp only [sendLink]; simp only [Step.used,↓reduceIte,map_sub,wrap_step, ← add_sub_assoc]; rfl
                   rw [map_add,wrap_vec,add_assoc]
abbrev sign (p:Plaq) : ℝ:= if p.negative then -1 else 1
abbrev payHere (p:Plaq): G.Color := Work.F03.faceCurl (Work.F03.slotFace (walkSlot p.face p.start) x) (arm G m 1 A)
lemma costOriented (p:Plaq): Pinned.read (sendLink x A) p= sign p • payHere x A p:= by
   unfold payHere Work.F03.faceCurl; rw [← fundamental]
   have hp:=orient_wrap x A p.start (square p.face.val.1 p.face.val.2); unfold Work.F03.slotFace; unfold Pinned.read sign; simp only [walkSlot_end]; rw [hp,add_comm x]; split<;> simp [walkSlot]
lemma adjoint_here (s:Slot)(u:G.El): Work.F03.faceCurl (Work.F03.slotFace s x) (arm G m 1 (stain u A))= G.adjoint u (Work.F03.faceCurl (Work.F03.slotFace s x) (arm G m 1 A)):= by
    let p:= Work.F03.slotFace s x; let a₀ := arm G m 1 (stain u A); let b:= arm G m 1 A; let V:= G.adjoint u;
    have he (i:Body 1 m):a₀ i=G.adjoint u (b i):= by unfold a₀ stain; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,(arm G m 1).apply_symm_apply]; rfl
    have hp(i:Edge (Site m)): collect G a₀ i=V (collect G b i):= he _
    have ht(l:Walk)(x:Site m): linkSum (collect G a₀) x l=V (linkSum (collect G b) x l):= by
       induction l generalizing x with
       | nil=> exact (map_zero _).symm
       | cons a l ih=> rw [linkSum,linkSum,ih,hp]; split <;> simp only [map_add,map_neg] -- hp rew conditional twice
    exact (fundamental G a₀ p.1 p.2).symm.trans ((ht _ _).trans (congr_arg V (fundamental G b p.1 p.2)))
end YM.QuadraticLocal.Poetry.Pinned
