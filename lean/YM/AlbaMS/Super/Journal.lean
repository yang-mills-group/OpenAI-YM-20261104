import YM.AlbaMS.Super.Epsilon

/-!
# Wick path verification at nil parameters

Cap ensures power sums on `touch`. Not a density comparison in exponentiating
an infinite-volume estimate. This verification is used on finite volumes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function Polynomial IsNilpotent
open scoped BigOperators Classical Polynomial
variable {ι R : Type*} [CommRing R] [Algebra ℚ R] {ρ : ι→Bool}
variable {F G I : Coil ρ R} {k g K : ι→ι→R} {s : Finset ι} {m n : ℕ} {Y : Coil ρ R[X]} {P : ℕ → Coil ρ R}

def falt (R : Type*) [CommRing R] [Algebra ℚ R] (n : ℕ) := algebraMap ℚ R (↑n.factorial : ℚ)⁻¹
@[simp] lemma falt_one : falt R 0=1:=by simp [falt]
lemma falt_succ (n) : ((n+1:ℕ):R)*falt R (n+1)=falt R n:=by
  unfold falt; rw [← map_natCast (algebraMap ℚ R) (n+1),← map_mul,Nat.factorial_succ,Nat.cast_mul]; field_simp

def pe (k : ι→ι→R)(s : Finset ι)(j : ℕ): Coil ρ R→ₗ[R] Coil ρ R:= falt R j • touch k s ^ j
def twig (k : ι→ι→R)(s : Finset ι)(j : ℕ): Coil ρ R→ₗ[R] Coil ρ R:= ∑ i∈ Finset.range (j+1),pe k s i
lemma pe_apply : pe k s m F= falt R m • (touch k s ^ m) F:= rfl
@[simp] lemma pe_zero : pe k s 0 F=F:=by rw [pe_apply,falt_one,one_smul,pow_zero]; rfl
lemma pe_step (i) (F : Coil ρ R) : ((i+1:ℕ):R) • pe k s (i+1) F = touch k s (pe k s i F):=by simp_rw [pe_apply,pow_succ',smul_smul,falt_succ,Module.End.mul_apply,map_smul]
lemma prod_pe_touch : pe k s (m+1) F=falt R (m+1) • (touch k s ^ m) (touch k s F):=by rw [pe_apply,_root_.pow_succ,Module.End.mul_apply]
omit [Algebra ℚ R] in
lemma killed (h:Cap F n)(H:n<2*m): (touch k s^m) F=0:=by
  induction m generalizing F n with
  | zero=> omega
  | succ m ih=>
    rw [_root_.pow_succ,Module.End.mul_apply]; obtain _|n:= n
    · rw [h.eroded, touch_const,map_zero]
    obtain _|n:= n
    · rw [touched _ _ _ h,map_zero]
    exact ih (Cap.touch _ n k s h) (by omega)
lemma pe_killed (h:Cap F n)(H:n<2*m):pe k s m F=0:= by rw [pe_apply, killed h H,smul_zero]
lemma twig_apply : twig k s m F=∑ i∈Finset.range (m+1),pe k s i F:= LinearMap.sum_apply ..
lemma twig_cut (h:Cap F n)(he:n≤2*m){i}(H:m≤i): twig k s m F = twig k s i F:=by
  rw [twig_apply,twig_apply]; refine Finset.sum_subset ?_ fun j _ hj=> pe_killed h (by rw [Finset.mem_range] at hj;omega); apply Finset.range_mono; omega
omit [Algebra ℚ R] in
lemma Cap.tree1 (h:Cap F n) : Cap ((Coil.touch k s ^m) F) n:=by
  induction m with
  | zero=> exact h -- defeq
  | succ i ih=> rw [pow_succ',Module.End.mul_apply];exact (ih.up (by omega : n≤n+2)).touch _ _ _ _
omit [Algebra ℚ R] in
lemma Tone.tree {p}(h:Tone p F)(H:Graded ρ false k): Tone p ((touch k s^m) F):=by
  induction m with | zero=> exact h|succ i ih=> rw [pow_succ',Module.End.mul_apply]; simpa using touch_tone _ _ _ _ _ ih H
lemma Cap.tree (h:Cap F n): Cap (twig k s m F) n:= (twig_apply (F:=F) (m:=m) (k:=k) (s:=s)) ▸ Cap.sum _ _ fun i _=>show Cap (falt R i • _) n from (Cap.tree1 (m:=i) (k:=k) (s:=s) h).smul _
lemma Tone.twig {p} (h:Tone p F)(H:Graded ρ false k): Tone p (twig k s m F):= (twig_apply (F:=F) (m:=m) (k:=k) (s:=s)) ▸ Tone.sum _ _ fun i _=> show Tone p (falt R i • _) from (Tone.tree (m:=i) (s:=s) h H).smul _
-- no limit on diagrams claimed when k=T with no nil order and no finite rank.
def wither (k : ι→ι→R)(s:Finset ι)(F : Coil ρ R):= if h:FinRank F then twig k s h.choose F else 0
lemma withers (h:Cap F n)(t:n≤2*m): wither k s F=twig k s m F:=by
  let V:FinRank F:=⟨_,h⟩; unfold wither; rw [dif_pos V]; have H:= V.choose_spec; exact (twig_cut H (by omega : V.choose ≤ 2*V.choose) (le_max_left _ m)).trans ((twig_cut h t (le_max_right V.choose _)).symm)

lemma proletariat {n:ℕ}(hn:0<n)(h:(n:R) • F=(n:R) • G): F=G:= by
  simp_rw [Nat.cast_smul_eq_nsmul,← Nat.cast_smul_eq_nsmul ℚ] at h
  let _ : IsAddTorsionFree (Coil ρ R):= IsAddTorsionFree.of_module_rat _; exact smul_right_injective (Coil ρ R) (show (n:ℚ) ≠ 0 by exact_mod_cast hn.ne') h
lemma journal (h:derive Y=touch (next k) s Y): atom m Y = pe k s m (line ρ 0 Y):=by
  induction m with
  | zero=> simp
  | succ m ih=>
    apply proletariat (Nat.zero_lt_succ m);rw [← step,h, atom_touch,ih,pe_step]
lemma spectrum (h:derive Y= touch (next k) s Y)(ht:FinRank (line ρ 0 Y)): line ρ 1 Y=wither k s (line ρ 0 Y):=by
  have he: Y=path ht.choose (fun i => pe k s i (line ρ 0 Y)):=by
    apply atoms; intro m; rw [path_atom, journal h]; intro i hi; exact pe_killed ht.choose_spec (by omega)
  calc
    _ = line ρ 1 (path ht.choose (fun i=> pe k s i (line ρ 0 Y))) := congr_arg _ he
    _ = _:=by rw [path_stop,withers ht.choose_spec (by omega : ht.choose ≤ 2*ht.choose),twig_apply]

lemma diary (g:Graded ρ false k)(h:Tone false Y)(H:IsNilpotent Y)
    (hr:derive Y=touch (next k) s Y-halve R[X] • cross false (next k) s Y Y) (tv: FinRank (line ρ 0 Y)) :
    exp (-(line ρ 1 Y)) = wither k s (exp (-(line ρ 0 Y))) := by
  have hr0 (b:R): line ρ b (exp (-Y))=exp (-(line ρ b Y)):=by rw [map_exp H.neg, map_neg]
  rw [← hr0 1,← hr0 0]; refine spectrum ?_ (hr0 0 ▸ tv.neg.exponent)
  rw [swept derives h.neg H.neg, touch_exp h.neg (next_graded false _ g) H.neg, map_neg,map_neg,hr];
  simp_rw [← from_tether (F:=-Y), map_neg,LinearMap.neg_apply,from_tether,neg_neg]; congr 1; abel
lemma logs (g:Graded ρ false k)(h:∀ i,n<i→P i=0)(hp:∀ i,Tone false (P i))(H:∀ i,IsNilpotent (P i))(ht:∀ j, ((j+1:ℕ):R) • P (j+1)=touch k s (P j)-halve R • ∑ i∈ Finset.antidiagonal j,cross false k s (P i.1) (P i.2))(tv:FinRank (P 0)): exp (-(∑ i∈Finset.range (n+1), P i))=wither k s (exp (-(P 0))):=by
  let Y:= path n P
  have hs:line ρ 0 Y=P 0:= (beg ..).trans (path_atom P 0 n h)
  rw [← hs,← path_stop]; exact diary g (Tone.path false P n hp) (path_nil P n hp H) (step_cross Y _ _ _ _ g h ht rfl) (hs.symm ▸ tv)
end YM.MSBar.Bric.Coil
