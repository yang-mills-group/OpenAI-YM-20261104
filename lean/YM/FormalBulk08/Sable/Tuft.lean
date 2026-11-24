import YM.FormalBulk08.Sable.Reach

/-! Weighted assembly preserving a declared held slot. No
premature charge paid just for shifting center. Important for physical-unit
roots and ordinary lattice before a soft read.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Filter Function Next.Free Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge} {I V:Type} {m n:ℕ} {D:Reach V} {σ η A B :ℝ} {a x:V}
abbrev tuft (D:Reach V)(x a:V)(v:chain V m):=herb D x (Fin.cons a v:chain V (m+1))
lemma tuft_turn (D:Reach V)(v:chain V m): tuft D x a v= tuft D a x v:= by
    let f:chain V (m+1+1):= Fin.cons a (Fin.cons x v); let i:Fin (m+1):=0; let j:Fin (m+1+1):=0
    have he:f ∘ (Equiv.swap j i.succ)=Fin.cons x (Fin.cons a v):= by
       funext k; cases k using Fin.cases with
       | zero=> dsimp only [comp_apply];change f ((Equiv.swap j i.succ) j)= _; rw [Equiv.swap_apply_left];rfl
       | succ k=> cases k using Fin.cases with
          | zero=> dsimp only [comp_apply];change f ((Equiv.swap j i.succ) i.succ)= _;rw [Equiv.swap_apply_right];rfl
          | succ k=> change f ((Equiv.swap j i.succ) _)=_; rw [Equiv.swap_apply_of_ne_of_ne]; exact Fin.cons_succ .. |>.trans rfl; exact Fin.succ_ne_zero _; exact fun h=> Fin.succ_ne_zero _ (Fin.succ_inj.mp h)
    change wide D _=wide D f; rw [←he,wide_turn]
lemma tuft_away (D:Reach V)(y:V)(v:chain V m):tuft D x a v ≤ tuft D x y v + D.d a y:= by
    rw [tuft_turn D v, tuft_turn D (a:=y)]; exact cloth ..
lemma tuft_plus (D:Reach V)(p:chain V m)(q:chain V n) : tuft D x a (Fin.append p q)≤ tuft D x a p+herb D a q:= by
    let T : chain V (m+n+2) :=Fin.cons a (Fin.cons x (Fin.append p q)); let V' : chain V (m+1+n+1):= Fin.cons a (Fin.append (Fin.cons x p : chain V (m+1)) q)
    rw [tuft_turn D (Fin.append p q),tuft_turn D p]; have he :wide D V'≤tuft D a x p+herb D a q:= by
       simpa only [tuft,herb,V',Reach.self,add_zero] using (meet_wide (D:=D) a a (Fin.cons x p : chain V (m+1)) q)
    have ht(i:Fin (m+n+2)):∃ k:Fin (m+1+n+1),T i=V' k:= by
       cases i using Fin.cases with
       | zero=>exact ⟨0,rfl⟩
       | succ i=> cases i using Fin.cases with
         | zero=> exact ⟨(Fin.castAdd n (0:Fin (m+1))).succ,by simp [T,V']⟩
         | succ i=> cases i using Fin.addCases with
           | left i=> exact ⟨(Fin.castAdd n i.succ).succ,by simp [T,V']⟩
           | right i=> exact ⟨(Fin.natAdd (m+1) i).succ,by simp [T,V']⟩
    choose f h using ht; refine le_trans ?_ he;change wide D T ≤ _; exact known_wide _ _ _ fun i j=>by rw [h,h];exact reached ..

def heft (D:Reach V)(η:ℝ)(o a:V)(T:Tile V m):ℝ≥0∞:=∑' v,Gorge.shine η (tuft D o a v)*‖T v‖ₑ
lemma heft_p (T:Tile V (n+1))(η:ℝ)(D:Reach V)(o:V) : (∑' v, penon D o η T v)=∑' x:V,heft D η o x (shed T x):= by
   rw [←Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (n+1)=>V)), ENNReal.tsum_prod'];rfl
lemma vapor_plus (T K: Tile V m)(o a:V): heft D η o a (T+K) ≤ heft D η o a T + heft D η o a K:= by
   unfold heft; rw [←ENNReal.tsum_add]; refine ENNReal.tsum_le_tsum fun v=> ?_; rw [←mul_add];gcongr; exact enorm_add_le ..
lemma vapor_scale (T:Tile V m)(o:V)(c:ℝ):heft D η o a (c • T)=‖c‖ₑ*heft D η o a T := by
   unfold heft; rw [←ENNReal.tsum_mul_left]; apply tsum_congr; intro v; rw [Pi.smul_apply, smul_eq_mul, enorm_mul,mul_left_comm]
lemma vapor_sum (P:Finset I)(T:I→ Tile V m): heft D η x a (∑ i∈P,T i)≤ ∑ i∈P,heft D η x a (T i):= by
   induction P using Finset.induction with
   | empty=> simp [heft]
   | @insert i P he ih=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (vapor_plus ..).trans (add_le_add_right ih _)
lemma vapor_swap (T:Tile V m)(o:V)(s:Equiv.Perm (Fin m)): heft D η o a (fun v=>T (v ∘ s))=heft D η o a T:= by
   unfold heft; rw [←Equiv.tsum_eq (Equiv.arrowCongr s.symm (Equiv.refl V)) (fun v=> Gorge.shine η (tuft D o a v)* ‖T v‖ₑ)]; apply tsum_congr; intro j; change _=Gorge.shine η (tuft D o a (j∘s))* _
   let f:= Equiv.Perm.decomposeFin.symm (0,s); let g := Equiv.Perm.decomposeFin.symm (0,f); have he : Fin.cons o (Fin.cons a (j∘s)) =(Fin.cons o (Fin.cons a j) : chain V (m+1+1)) ∘ g:= by ext1 i; cases i using Fin.cases with
                                                                                                                                                                                                   | zero=> simp [f,g]
                                                                                                                                                                                                   | succ i=>cases i using Fin.cases <;> simp [g,f,Equiv.Perm.decomposeFin_symm_apply_succ]
   rw [show tuft D o a (j ∘ s)=wide D ((Fin.cons o (Fin.cons a j)) ∘ g) from congr_arg _ he, wide_turn]; rfl
lemma polish_s (T:Tile V m): heft D η x a (sand T) ≤ heft D η x a T := by
   let S:= Equiv.Perm (Fin m); let M:ℝ:= Fintype.card S; have hm:0<M:=Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩)
   let f i:Tile V m:= fun v=> T (v ∘ (i:Equiv.Perm (Fin m))); rw [show sand T=M⁻¹ • ∑ s,f s from (by funext v; simp only [sand,Pi.smul_apply, Finset.sum_apply,smul_eq_mul]; rw [div_eq_mul_inv,mul_comm]),vapor_scale]
   refine (mul_le_mul_right (vapor_sum ..) _).trans_eq ?_; unfold f;simp_rw [vapor_swap];rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hm.le), show (Fintype.card S:ℝ≥0∞)=ENNReal.ofReal M by simp [M],← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), inv_mul_cancel₀ hm.ne', ENNReal.ofReal_one,one_mul]
lemma loom_away (z:V)(h:D.d a z≤ n)(hp:0≤η)(T:Tile V m) : heft D η x a T≤ Gorge.shine η n *heft D η x z T:= by
   unfold heft; rw [← ENNReal.tsum_mul_left]; exact ENNReal.tsum_le_tsum fun v=> le_trans (mul_le_mul_left (shine_le η hp (show tuft D x a v ≤ n+tuft D x z v from (tuft_away D z v).trans ((add_le_add_right h _).trans (le_of_eq (add_comm _ _))))) _) (by rw [shine_add,mul_assoc])
lemma vapor_clasp (hp:0≤η) (T: Tile V m)(K:Tile V n): heft D η x a (clutch T K)≤ heft D η x a T *∑' v,penon D a η K v:= by
   unfold heft; rw [←Equiv.tsum_eq (castle V m n),ENNReal.tsum_prod',← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro u; rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v
   have hh:=shine_le η hp (tuft_plus D (x:=x) (a:=a) u v); rw [shine_add] at hh; refine le_trans (mul_le_mul_left hh _) (le_of_eq ?_); rw [show clutch T K _=T u * K v from (by simp [castle,clutch,Function.comp_def]), enorm_mul];unfold penon; ring
lemma polish_grade (T:Tile V m)(h:m=n): heft D η x a (lengthen h T)=heft D η x a T:= by subst n;rfl
end YM.FormalBulk08.Sable
