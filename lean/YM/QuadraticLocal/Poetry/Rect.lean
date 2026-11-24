import YM.Push.LOOP_COEFFICIENT.LoopRow
import YM.Extra.ITERATION_NO_LOSS.Atoms
/-! Adapts (borrows) `YM/RG02/Pinned/{Fields,Rectangles}.lean`, staff over exactly this closure.T -/
/-!
# Telescoping pinned edges into canonical path slots

At this stage work only with linear field directions. Actual cover order,
length, and curvature conventions. Remainders on real nonlinear group
fields are another task. Rank E forthcoming.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Pinned
open Function Filter Finset Tensor
open Lattice Wilson RG Precision Exterior Tree
open Laurent Bloch Push Push.Loops
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {R A : Type*} [AddCommGroup R] [One R] [AddCommGroup A]
lemma along_walk (U : Lattice.Links R A) (x : Four R) (a b : Walk) : linkSum U x (a++b)=linkSum U x a+linkSum U (stop x a) b := by induction a generalizing x with
  | nil=> simp [linkSum,stop]
  | cons i a h=> rw [List.cons_append,linkSum,linkSum,stop,h,add_assoc]
lemma backWalk (U : Lattice.Links R A) (x : Four R) (a : Walk) : linkSum U (stop x a) (Lattice.reverse a)= - linkSum U x a := by
  induction a generalizing x with
  | nil=> simp [Lattice.reverse,stop,linkSum]
  | cons i a h=>
     rw [reverse,List.reverse_cons,List.map_append,stop,along_walk,show List.map Step.rev _=Lattice.reverse a from rfl,h (x+i.vec), reverse_stop]
     cases i with
     | mk d b=> cases b <;> simp [linkSum,Step.used,Step.rev,Step.vec,sub_eq_add_neg]
structure Plaq where
   negative : Bool
   start : Cover
   face : PlaqAxes
variable (U : Lattice.Links ℤ A)
def read (q:Plaq) : A:=
   let v:= linkSum U q.start (square q.face.val.1 q.face.val.2)
   if q.negative then -v else v
private lemma face_eq (x : Cover) (i j : Axis) : linkSum U x (square i j)=U (x,i)+U (x+step i,j)-U (x+step j,i)-U (x,j):=by
   simp only [posDir,negDir,square,linkSum,Step.vec,Step.used,↓reduceIte,Bool.false_eq_true]
   rw [show x+step i+step j-step i=x+step j by abel,show x+step i+step j+(-step i)=x+step j by abel]; simp; abel
lemma step_one (i:Axis) : size (step i : Cover) = 1:=by simp [size,_root_.apply_ite Int.natAbs]
private lemma width_ (x : Cover)(i: Axis) : size (x-step i) ≤ size x+1:=by rw [sub_eq_add_neg]; exact (size_add ..).trans_eq (by rw [size_neg,step_one])
private lemma plaq_walk (x : Cover)(i j : Axis)(he : i ≠ j) (η : Bool) : ∃ q:Plaq, size q.start ≤ size x ∧ ∀ U:Lattice.Links ℤ A, Pinned.read U q = if η then -linkSum U x (square i j) else linkSum U x (square i j) := by
    rcases lt_or_gt_of_ne he with h|h
    · exact ⟨⟨η,x,(⟨(i,j),h⟩)⟩,le_rfl,fun _=>rfl⟩
    refine ⟨⟨!η,x,⟨(j,i),h⟩⟩,le_rfl,fun U=>?_⟩
    unfold Pinned.read
    cases η <;> simp only [Bool.not_true,Bool.not_false, ↓reduceIte,Bool.false_eq_true, face_eq] <;> abel
private lemma swab (x : Cover) (a : Step) (b: Axis)(h:a.dir ≠ b): ∃ q:Plaq,size q.start ≤ size x+1 ∧ ∀ U:Lattice.Links ℤ A,
    linkSum U x [a,posDir b]-linkSum U x [posDir b,a]=Pinned.read U q := by
    cases a with
    | mk i η=> cases η
               · obtain ⟨q,hq,Q⟩:=Pinned.plaq_walk (A:=A) x i b h false; refine ⟨q,hq.trans (Nat.le_succ _),fun U=>?_⟩
                 rw [Q]; simp [linkSum,Step.used,posDir,Step.vec] -- don't expand RHS square
                 rw [face_eq]; abel
               obtain ⟨q,hq,Q⟩:=Pinned.plaq_walk (A:=A) (x-step i) i b h true
               refine ⟨q,hq.trans (width_ x i),fun U=>?_⟩; rw [Q,face_eq]
               simp [linkSum,posDir,Step.vec,Step.used]
               rw [show x+step b-step i=x-step i+step b by abel,sub_eq_add_neg x]; abel
private lemma shift_span (d:Step): size (d.vec:Cover) ≤ 1:= by unfold Step.vec; split<;> simp [size_neg,step_one]
private lemma exchange (x : Cover)(L:Walk)(b:Axis)(he : ∀ s∈L,s.dir ≠ b) : ∃ W:List Plaq, W.length = L.length ∧
    (∀ q∈W,size q.start ≤ size x+ L.length) ∧ ∀ U:Lattice.Links ℤ A,linkSum U x (L++[posDir b])-linkSum U x (posDir b::L)=(W.map (Pinned.read U)).sum:=by
  induction L generalizing x with
  | nil=> exact ⟨[],rfl,by simp,fun _=>by simp⟩
  | cons i L h=>
     obtain ⟨W,hW,Q,H⟩:= h (x+i.vec) (fun s hs=>he s (List.mem_cons_of_mem i hs))
     obtain ⟨q,hq,V⟩:=Pinned.swab (A:=A) x i b (he i List.mem_cons_self)
     refine ⟨q::W,by simp [hW],?_ ,fun U=>?_⟩
     · intro u hx; apply (List.mem_cons.mp hx).elim
       · rintro rfl; simp only [List.length_cons]; omega
       intro h'; refine (Q u h').trans ?_; simp only [List.length_cons]; exact le_trans (Nat.add_le_add_right ((size_add ..).trans (Nat.add_le_add_left (shift_span _) _)) _) (le_of_eq (by omega))
     let z : Cover := x+i.vec
     change linkSum U x _-linkSum U x ([posDir b,i] ++ L)=_
     rw [along_walk U x [posDir b,i] L,List.map_cons,List.sum_cons,← V U,← H U,List.cons_append]
     have ht : linkSum U z (posDir b :: L)= linkSum U z [posDir b]+linkSum U (stop z [posDir b]) L:= along_walk U z [posDir b] L
     dsimp only [z] at ht
     have hS : stop (x+i.vec) [posDir b] = stop x [posDir b,i] := by simp only [stop]; abel
     rw [linkSum, ht,hS, show linkSum U x [i,posDir b]= _ from along_walk U x [i] [posDir b]]
     simp only [linkSum,stop]; abel
section straight_
variable (d:ℤ)(x : Cover)(b:Axis)
private def extStep : Walk := straight b d++[posDir b]
private lemma plus (a:ℕ) : straight b (Int.ofNat a)=List.replicate a (posDir b) := by unfold straight; rw [decide_eq_false (by exact not_lt.mpr (Int.natCast_nonneg _))]; rfl
private lemma minus (a:ℕ) : straight b (Int.negSucc a)=List.replicate (a+1) (negDir b):=by unfold straight; rw [decide_eq_true (by omega)]; rfl
private lemma minus' (a:ℕ): straight b (-↑a)=List.replicate a (negDir b):=by cases a; simp [straight]; exact Pinned.minus b _ -- order
private lemma replicate (k:ℕ)(a:Step) : List.replicate (k+1) a=List.replicate k a++[a]:=by simpa only [List.replicate_one] using List.replicate_add k 1 a
private lemma straight_next : linkSum U x (straight b (d+1))=linkSum U x (extStep d b):=by
    cases d with
    | ofNat a=> unfold extStep; rw [show Int.ofNat a+1=Int.ofNat (a+1) from rfl, Pinned.plus b,Pinned.plus b,replicate a]
    | negSucc a=>
       unfold extStep; rw [Pinned.minus b,replicate a,show Int.negSucc a+1= -↑a by omega,minus' b]
       rw [List.append_assoc,along_walk]; simp [linkSum,Step.used,Step.vec,posDir, negDir,sub_eq_add_neg]
private lemma straight_end_step : stop x (straight b (d+1))=stop x (extStep d b):=by
   unfold extStep; rw [stop_append,straight_stop,straight_stop,add_smul,one_smul]; simp [stop]; abel
end straight_
-- fixed order chosen independent of marking at all iterations
abbrev stride_ (x : Cover) := route (0 : Cover) x (1:Lattice.Order)
private lemma noShift (x:Cover) (b:Axis) (l:List Axis) (h:b∉l) : axisRoute 0 x l=axisRoute (0:Cover) (x+step b) l:=by
   induction l with
   | nil=> rfl
   | cons a l he=>
                    have ht := he (fun hv=> h (List.mem_cons_of_mem _ hv)); change straight a _ ++ axisRoute 0 x l=straight a _ ++ axisRoute 0 (x+step b) l
                    rw [ht]; simp only [Pi.add_apply]; simp [show a≠b from fun hn=> h (hn ▸ List.mem_cons_self)]
private lemma separate_axes (x:Cover)(b:Axis)(l:List Axis)(h:b∉l)(i : Step)(he:i∈axisRoute 0 x l) : i.dir ≠ b := by
   rcases List.mem_flatMap.mp he with ⟨p,hp,H⟩
   have hx:=List.eq_of_mem_replicate H
   exact fun he=> h ((show p=b from (congrArg Step.dir hx).symm.trans he) ▸ hp)

def lead (x : Cover) (i:Axis) := linkSum U 0 (stride_ x++[posDir i])-linkSum U 0 (stride_ (x+ step i))
lemma rectangles (x : Cover) (i:Axis) : ∃ W: List Plaq,W.length ≤ size x ∧ (∀ q∈ W,size q.start ≤ size x) ∧ ∀ U:Lattice.Links ℤ A,lead U x i= (W.map (Pinned.read U)).sum := by
    have hX : i∈ allAxes 1:= List.mem_map.mpr ⟨i,List.mem_finRange _,rfl⟩
    obtain ⟨p,q,hq⟩:=List.append_of_mem hX
    have ht:i∉p ∧ i∉q:=by
       have he : (p++i::q).Nodup:= hq ▸ (List.nodup_finRange 4).map (1:Lattice.Order).injective
       have T:=List.nodup_append.mp he
       exact ⟨fun hi=> T.2.2 _ hi _ List.mem_cons_self rfl, (List.nodup_cons.mp T.2.1).1⟩
    let P:=axisRoute 0 x p
    let L:=straight i (x i)
    let Z:=axisRoute 0 x q
    have hh : stride_ x=P++L++Z:=by unfold stride_ route P L Z; rw [hq]; simp [axisRoute, List.append_assoc]
    have hx : stride_ (x+step i)= P++straight i (x i+1)++Z:=by unfold stride_ route P Z; rw [noShift x i p ht.1,noShift x i q ht.2,hq]; simp [axisRoute]
    obtain ⟨W,hW,H,V⟩:= exchange (A:=A) (stop 0 (P++L)) Z i (separate_axes x i q ht.2)
    have he : (P++L).length+Z.length=size x:= (List.length_append).symm.trans (hh ▸ (Extra.Iteration.route_length (0:Cover) x 1 |>.trans (by rw [sub_zero])))
    refine ⟨W,by omega,fun i hi=> (H i hi).trans ?_,fun U=>?_⟩
    · have he' : size (stop 0 (P++L)) ≤ (P++L).length:= by simpa [size] using Push.Loops.size_stop (0:Cover) (P++L)
      omega
    have hu : linkSum U 0 (stride_ (x+step i))=linkSum U 0 ((P++L)++(posDir i :: Z)):=by
       rw [hx]
       have hz (W:Walk) : linkSum U 0 (P++W++Z)=linkSum U 0 P+linkSum U (stop 0 P) W+linkSum U (stop (stop 0 P) W) Z:=by rw [along_walk,along_walk,stop_append]
       have hP: (P++L)++(posDir i :: Z)=P++extStep (x i) i++Z :=by simp [extStep,L]
       rw [hP,hz,hz, Pinned.straight_next, Pinned.straight_end_step]
    unfold lead; rw [hu,hh,← V U, List.append_assoc (P++L),along_walk U 0 (P++L),along_walk U 0 (P++L)]; abel
end YM.QuadraticLocal.Poetry.Pinned
