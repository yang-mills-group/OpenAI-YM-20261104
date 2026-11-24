import YM.RG11Scheme.Bell.Maple
import YM.RG11Scheme.Bell.Near

/-! Filtration by native lattice differences; transforms into top continuum homogeneous symbol. Use top derivative laws only on polynomial arrays. -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.RG11Scheme.Bell
open Filter Function Set Maxwell Mesh Lattice Stencil Stencil.Shot Tensor Next.Rank.Radian
open scoped BigOperators Classical Topology
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] {d:ℕ}
section one
variable {P R Q: Tensor.T E4 E d} {f g:Cover→ E}
-- at top
structure Says (f : Cover→ E)(P : Tensor.T E4 E d) : Prop where
   sym : Tensor.Sym P
   grade : f∈hill E d
   rank : ∀ D:List Axis,D.length=d→ go D f 0=go D (traces P) 0
lemma aimed (f:Cover→E)(h:f∈hill E d): Says f (cranium d f):=⟨symmetrize_sym _,h,fun D h=> skates _ _ D h⟩
lemma own (h:Tensor.Sym P) : Says (traces P) P:=⟨h,traces_grade _,fun _ _=> rfl⟩
omit [CompleteSpace E] in
lemma Says.atlas (h:Says f P)(D:List Axis)(hd:D.length=d)(x:Cover) : go D f x=go D (traces P) 0 := by
    have he: go D f∈hill E 0:= by have := sliced_at D h.grade; simpa only [hd,Nat.sub_self] using this
    exact (hill_const_iff.mp he x).trans (h.rank D hd)
omit [CompleteSpace E] in
lemma Says.zero : Says (0:Cover→ E) (0:Tensor.T E4 E d):= ⟨fun _ _=>rfl,(hill E d).zero_mem,fun D _=>by rw [show traces (0:Tensor.T E4 E d)=0 from funext fun _=>rfl]⟩
omit [CompleteSpace E] in
lemma Says.plus (h:Says f P)(hp:Says g Q): Says (f+g) (P+Q) := by
   refine ⟨fun x c=> congrArg₂ (·+·) (h.sym x c) (hp.sym x c),(hill E d).add_mem h.grade hp.grade,?_⟩
   intro D hd
   rw [Point.plus_go, h.rank _ hd, hp.rank _ hd]; exact (Point.plus_go (traces P) (traces Q) D 0).symm
omit [CompleteSpace E] in
lemma Says.scalar (h:Says f P)(r:ℝ): Says (r • f) (r • P) := by
   refine ⟨fun x c=> congrArg (r • ·) (h.sym x c),(hill E d).smul_mem r h.grade,fun D hd=>?_⟩
   rw [show traces (r • P)=r • traces P from funext fun _=>rfl]
   change ladder D (r • f) 0=ladder D (r • traces P) 0
   rw [map_smul,map_smul]; exact congrArg (r • ·) (h.rank D hd)
omit [CompleteSpace E] in
lemma Says.minus (h:Says f P)(hp:Says g Q): Says (f-g) (P-Q) := by simpa only [neg_smul,one_smul, ← sub_eq_add_neg] using h.plus (hp.scalar (-1))
lemma Says.agrees (hf:Says f P)(hg:Says f Q): P=Q := by
   ext1 v; have he (u:E4): ∑ i:Axis,u i • basis i=u:= by ext i; simp
   have hp γ : P (basis ∘ γ)=Q (basis ∘ γ):= smul_right_injective E (show (↑d.factorial:ℝ)≠0 by positivity) ((deliver P hf.sym γ 0).symm.trans (((hf.rank _ (by simp)).symm.trans (hg.rank _ (by simp))).trans (deliver Q hg.sym γ 0)))
   have hx : v=fun p:Fin d=> ∑ i:Axis, v p i • basis i:= funext fun i=> (he _).symm
   nth_rw 1 2 [hx]
   -- Multilinear map on basis
   change P.toMultilinearMap _=Q.toMultilinearMap _
   rw [MultilinearMap.map_sum_finset, MultilinearMap.map_sum_finset];apply Finset.sum_congr rfl; intro p hp'; simp_rw [P.toMultilinearMap.map_smul_univ,Q.toMultilinearMap.map_smul_univ]; exact congrArg _ (hp p)
omit [CompleteSpace E] in
lemma Says.shift (hf:Says f P)(x:Cover): Says (fun z=>f (z+x)) P:=⟨hf.sym,rise_cut _ hf.grade,fun D hd=>by rw [Mesh.shifted]; exact hf.atlas D hd _⟩
end one
variable {f g:Cover→ E}{A : Tensor.T E4 E (d+1)}
def prime (v:Axis)(P:Tensor.T E4 E (d+1)) := ((↑(d+1:ℕ):ℝ)) • P.curryLeft (basis v)
lemma Says.different (h:Says f A) (i:Axis) : Says (go [i] f) (prime i A) := by
   have he : Sym (prime i A):= fun v s=> congrArg (fun x:E=>((↑(d+1:ℕ):ℝ)) • x) (freeze_sym A h.sym (basis i) v s)
   refine ⟨he,sliced h.grade i,fun D hd=>?_⟩
   let γ := fun x:Fin d=> (D.reverse.get ⟨x.val,(show (x:ℕ)<_ by rw [List.length_reverse,hd]; exact x.isLt)⟩)
   have hγ : D=(List.ofFn γ).reverse:= by rw [show List.ofFn γ=D.reverse from (list_from (D:=D.reverse) (d:=d) (by simp [hd])).symm]; simp
   rw [←go_concat,hγ,h.rank _ (by simp), leading (prime i A)]
   have hx : (List.ofFn γ).reverse ++ [i] = (List.ofFn (Fin.cons i γ)).reverse := by rw [List.ofFn_succ, List.reverse_cons]; simp
   rw [hx,leading,← hx,Hinge.dV_append,flat_shade A h.sym];exact rfl
lemma Says.subtract (h:Says f A): f - traces A ∈ hill E d := by
   apply (lower_iff ((hill E _).sub_mem h.grade (traces_grade _))).2
   exact fun D he=> by change ladder D _ 0=_; rw [map_sub]; exact sub_eq_zero.mpr (h.rank D he)
omit [CompleteSpace E] in
lemma Says.retain {f:Cover→E} (u:Says f A) {P:Cover→ E}(h:f-P∈hill E d): Says P A := by
   have eq:f-(f-P)=P:=sub_sub_cancel ..; rw [←eq]
   refine ⟨u.sym,(hill E _).sub_mem u.grade (hills (Nat.le_succ d) h),fun D hd=>?_⟩
   change ladder D (f-(f-P)) 0=_; have he := (show ∀ W:List Axis,_ → go W (f-P) = 0 from h) D (by omega : D.length>d)
   rw [map_sub, show ladder D (f-P)=_ from he]; simpa only [Pi.sub_apply,Pi.zero_apply,sub_zero] using! u.rank D hd
omit [CompleteSpace E] in
lemma stop_graded {f:Cover→ E}{d:ℕ}(h:f∈hill E (d+2)) i : stoptime f i∈ hill E d := by
   rw [show stoptime f i = (fun x=>go [i,i] f (x+ -step i)) from funext fun x=>by rw [← sub_eq_add_neg]; exact stop_eq ..]; apply rise_cut
   have he:=sliced_at [i,i] h; simpa only [List.length_cons,List.length_nil, Nat.add_zero, zero_add, Nat.reduceAdd,Nat.add_sub_cancel] using he
omit [CompleteSpace E] in
lemma quake_graded {f:Cover→ E}{d:ℕ}(h:f∈hill E (d+2)) : quake f∈hill E d:= by rw [show quake f=∑ i:Axis,stoptime f i from funext fun x=>by unfold quake; rw [Finset.sum_apply];exact rfl]; apply Submodule.sum_mem; exact fun i _=> stop_graded h i
end YM.RG11Scheme.Bell
