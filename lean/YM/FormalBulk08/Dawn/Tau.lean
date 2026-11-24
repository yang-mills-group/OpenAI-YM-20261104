import YM.FormalBulk08.Dawn.Sheaf

/-! Canonical multi-index letters and cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Filter Set Function Lattice Chapel Tensor
open scoped Topology BigOperators Classical ContDiff
variable {D j h :ℕ}

def granary (a:Fin j→ Axis) : Seasons:=∑ i,grain (a i)
lemma granary_nil (a:Fin 0→Axis) : granary a=0:=by simp [granary]
lemma granary_cons (i:Axis)(a:Fin j→Axis):granary (Fin.cons i a : Fin (j+1)→Axis)=granary a+grain i:=by simp [granary,Fin.sum_univ_succ,add_comm]
lemma stocked (a:Fin j→Axis): upper (granary a)=j:=by
   induction j with
   | zero=> simp only [granary_nil]; simp [upper]
   | succ j ih=> nth_rw 1 [← Fin.cons_self_tail a]; rw [granary_cons,upper_push,ih]
lemma granary_skim (a:Fin j→Axis)(i:Axis): granary a i=Fintype.card {x// a x=i}:=by
    unfold granary; rw [Finset.sum_apply]; simp_rw [grain,Fintype.card_subtype]; simp_rw [eq_comm (a:=i)]; exact (Finset.card_filter _ _).symm

def word (v: Brush D): Seasons:=granary v.2
lemma word_val (v : Brush D): upper (word v)=v.1.val:=stocked _
lemma same_word {a b : Brush D} (w:word a=word b)(f:Studio D): f.val a=f.val b:=by
   obtain ⟨g,rfl⟩:=portrayed D f; rcases a with ⟨l,a⟩;rcases b with ⟨m,b⟩
   have he:l=m:=Fin.ext (by rw [←word_val (Sigma.mk l a),w,word_val])
   subst m; let e : Equiv.Perm (Fin l.val):=Equiv.ofFiberEquiv (fun i=> Fintype.equivOfCardEq (show Fintype.card {x//b x=i}=Fintype.card {x//a x=i} by rw [←granary_skim,←granary_skim]; exact congr_fun w.symm i))
   have he i:a (e i)=b i:=Equiv.ofFiberEquiv_map ..
   ext1 x; change iteratedFDeriv ℝ _ _ _ (basis ∘ a)=iteratedFDeriv ℝ _ _ _ (basis ∘ b); rw [show basis ∘ b=(basis ∘ a) ∘ e from funext fun i=> (congr_arg basis (he i)).symm]; exact (Analysis.sym_Jet ((tends g l).contDiffAt) _ e).symm

lemma draw_any (p:Seasons) (hp:upper p≤D): ∃ v:Brush D,word v=p:=by
   generalize h : upper p=n
   induction n generalizing p with
   | zero=>
     refine ⟨⟨0,Fin.elim0⟩,?_⟩
     have he:p=0 := by ext i;exact Nat.le_zero.mp ((Finset.single_le_sum (f:=p) (fun _ _=> Nat.zero_le _) (Finset.mem_univ _)).trans (show (∑ i,p i)≤0 from h.le))
     rw [he]; apply granary_nil
   | succ n ih=>
     obtain ⟨i,hi⟩ : ∃ i:Axis,0< p i := by
       by_contra! he; have hx:(upper p)=0:=Finset.sum_eq_zero fun i _=>Nat.le_zero.mp (he i); omega
     obtain ⟨q,rfl⟩:= kick p i hi
     have he : upper q=n := by rw [upper_push] at h; omega
     obtain ⟨b,hb⟩:=ih q (by omega) he
     have hz:b.1.val=n:=by rw [←word_val,hb,he]
     refine ⟨⟨⟨b.1.val+1,by omega⟩,Fin.cons i b.2⟩,(granary_cons ..).trans (congr_arg (·+grain i) hb)⟩

lemma rose_root (p:Seasons): rose p 0=if p=0 then 1 else 0:=by
    split
    · subst p; simp [rose,petal]
    rename_i h; obtain ⟨i,hi⟩:=Function.ne_iff.mp h; change p i≠0 at hi;exact Finset.prod_eq_zero (Finset.mem_univ i) (by change petal i (p i) 0=0;simp [petal,hi])
lemma rose_atom (p:Seasons)(a:Fin j→Axis)(h:j≥upper p)(x:E4): iteratedFDeriv ℝ j (rose p) x (basis ∘ a) = if granary a=p then 1 else 0 := by
   induction j generalizing p with
   | zero=>
     have he:p=0 := by ext i;exact Nat.le_zero.mp ((Finset.single_le_sum (f:=p) (fun _ _=> Nat.zero_le _) (Finset.mem_univ _)).trans (show (∑ i,p i)≤0 from h))
     subst p; simp only [granary_nil, ↓reduceIte]; rw [iteratedFDeriv_zero_apply]; simp [rose,petal]
   | succ j ih=>
     let b:=Fin.tail a;let i:=a 0
     have he : basis ∘ a= Fin.cons (basis i) (basis ∘ b):=(Fin.cons_self_tail _).symm
     rw [he,Analysis.cons_inner (by exact (rose_smooth p).contDiffAt.of_le le_top)]
     rw [←Fin.cons_self_tail a, granary_cons]; change iteratedFDeriv ℝ j (Analysis.D (basis i) _) _ _=if granary b+grain i=p then 1 else 0
     by_cases hv : 0<p i
     · obtain ⟨q,rfl⟩:=kick p i hv
       rw [edge_deriv, ih]; simp
       rw [upper_push] at h; omega
     have hx:=show p i=0 from Nat.eq_zero_of_not_pos hv
     rw [rose_dead p i hx, show (0:E4→ℝ)=fun _=>0 from rfl, iteratedFDeriv_fun_zero,if_neg (show granary b+grain i ≠ p from fun he=>by have hz:=congr_fun he i; simp [grain,hx] at hz)];rfl
lemma rose_corner (p:Seasons)(a:Fin j→Axis): iteratedFDeriv ℝ j (rose p) 0 (basis ∘ a)=if granary a=p then 1 else 0:= by
   induction j generalizing p with
   | zero=> rw [iteratedFDeriv_zero_apply,granary_nil,rose_root]; simp only [eq_comm]
   | succ j ih=>
     let i:=a 0; let b:= Fin.tail a
     rw [show basis ∘ a=Fin.cons (basis i) (basis ∘ b) from (Fin.cons_self_tail _).symm, Analysis.cons_inner (by exact (rose_smooth p).contDiffAt.of_le le_top),←Fin.cons_self_tail a,granary_cons]
     change iteratedFDeriv ℝ j (Analysis.D (basis i) _) _ _=if granary b+grain i=p then 1 else 0
     by_cases h:0<p i
     · obtain ⟨q,rfl⟩:=kick p i h; rw [edge_deriv,ih]; simp
     have hx:=show p i=0 from Nat.eq_zero_of_not_pos h
     rw [rose_dead p i hx, show (0:E4→ℝ)=fun _=>0 from rfl, iteratedFDeriv_fun_zero, if_neg (show granary b+grain i≠p from fun he=>by have hz:=congr_fun he i;simp [grain,hx] at hz)]; rfl

def tint (D : ℕ)(p: Seasons):Garden D:=⟨rose p,(rose_smooth p).of_le (show (↑D:WithTop ℕ∞)≤ω from le_top)⟩
def cone (D : ℕ)(p:Seasons):Studio D:=portrait D (tint D p)
def finger {p:Seasons}(h:upper p ≤ D) : Brush D:= (draw_any p h).choose
def notch (p: Seasons)(h:upper p≤ D):= assess (finger h) origin
lemma notched {p:Seasons}(h:upper p≤D)(x:Studio D)(b:Brush D)(hx:word b=p): notch p h x=x.val b origin := by
    change x.val _ origin=_; exact DFunLike.congr_fun (same_word (a:=finger h) (((draw_any p h).choose_spec).trans hx.symm) x) origin
lemma notch_basis {p:Seasons}(h : upper p≤ D)(q: Seasons): notch p h (cone D q)= if p=q then 1 else 0:= by
   let b : Brush D:=finger h; have hb:word b=p:= (draw_any p h).choose_spec; rw [notched h _ b hb]; change iteratedFDeriv ℝ _ (rose q) 0 (basis ∘ b.2)=_; exact (rose_corner q b.2).trans (by rw [←hb];rfl)
end YM.FormalBulk08.Dawn
