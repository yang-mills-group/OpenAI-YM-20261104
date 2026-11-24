import YM.SignedWilsonExpansion.F9.Table
/-!
# A new-order coefficient is linear as a difference at fixed through-horizon prefix
-/
noncomputable section
set_option autoImplicit false
namespace YM.SignedWilsonExpansion.Commission
open Function Set Filter MeasureTheory PowerSeries WilsonCoeffUV.Mer.Xa XSpace XSpace.Normalize
open Tape
open scoped Topology ContDiff BigOperators Classical
variable {E:Type}[AddCommGroup E][Module ℂ E]
variable {n i j d:ℕ} {I: Type}
local notation "Ink" => PowerSeries ℂ
variable {x y:Ink}
section split
abbrev Ident (i:ℕ)(x y:Ink):Prop:= ∀ e< i,coeff e x= coeff e y
lemma ident_mul {u v:Ink} (p:Ident i x y)(q:Ident i u v): Ident i (x*u) (y*v):=fun e w=>by rw [coeff_mul,coeff_mul]; exact Finset.sum_congr rfl (fun i t=>by have h:= Finset.mem_antidiagonal.mp t; rw [p i.1 (by omega),q i.2 (by omega)])
lemma ident_pow (p:Ident i x y)(j:ℕ): Ident i (x^j) (y^j):=by induction j with| zero=>rw [pow_zero,pow_zero]; exact fun _ _=>rfl| succ i h=> rw [pow_succ,pow_succ]; exact ident_mul h p
lemma comp_root (p:constantCoeff x=0)(T:Tape.Table E n): composed T x 0=T 0:=by rw [composed,zero_add,Finset.range_one,Finset.sum_singleton,pow_zero,coeff_one]; simp
lemma comp_earlier (p:Ident i x y)(T:Tape.Table E n) (v:j< i): composed T x j=composed T y j:=by unfold composed; exact Finset.sum_congr rfl fun i _=> by rw [ident_pow p i j v]
lemma ident_priority (p:Ident i x y)(hq:constantCoeff x=0)(hv:constantCoeff y=0)(k:ℕ):coeff i (x^(k+2))= coeff i (y^(k+2)):=by
    rw [pow_succ x (k+1),pow_succ y (k+1), coeff_mul,coeff_mul]; -- pow_succ rewriting lhs twice fix rg
    refine Finset.sum_congr rfl (fun j hj=> ?_); have hz:= Finset.mem_antidiagonal.mp hj; by_cases he:j.2=0; · rw [he,coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,hq,hv,mul_zero,mul_zero]
    by_cases h:j.1=0; · rw [h,coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply,map_pow,map_pow,hq,hv]; simp
    rw [ident_pow p (k+1) j.1 (by omega),p j.2 (by omega)]
def paused (p:Fin n→Tape E): Fin n→ E:= fun i=>p i 0
def rider (p:Fin n→Tape E)(v:Normalize.Days n): Fin n→ E:= fun i=> p i (v (some i))
lemma heel (T:Tape.Table E n)(p:constantCoeff x=0)(v: Fin n→Tape E): coeff 0 (tabular (composed T x) v)= T 0 (paused v):=by rw [tab_coeff,Normalize.tally,Finset.finsuppAntidiag_zero, Finset.sum_singleton]; change composed T x 0 _= _; rw [comp_root p]; rfl
lemma compPriority (T:Tape.Table E n) (v:i≠0)(p:Ident i x y)(h1:constantCoeff x=0)(h2:constantCoeff y=0): composed T x i-composed T y i=(coeff i x-coeff i y) • T 1:=by
    unfold composed; rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 1]; · rw [pow_one,pow_one,sub_smul]
    · intro b hb hx; rcases b with _|_|b; simp; contradiction; rw [ident_priority p h1 h2 _, sub_self]
    intro h; exact False.elim (h (Finset.mem_range.mpr (by omega)))
lemma bud_single (v:Days n)(e:v∈tally i n)(j)(hv:v j=i): v=Finsupp.single j i:=by
    ext1 k; by_cases hx:k=j; · subst k; rw [hv, Finsupp.single_eq_same]
    rw [Finsupp.single_eq_of_ne hx]; have h:= Finset.add_sum_erase (Finset.univ:Finset (Option (Fin n))) (fun j=> v j) (Finset.mem_univ j); rw [(totaled v).mp e, hv] at h -- dubious rewrite
    have hz: ∑ a∈ Finset.univ.erase j,v a= 0:=by omega
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _=>Nat.zero_le (v k))).mp hz _ (Finset.mem_erase.mpr ⟨hx,Finset.mem_univ _⟩)
lemma bud_ne (v: Days n)(e:v∈tally i n)(j)(p:v≠ Finsupp.single j i): v j< i:= lt_of_le_of_ne (((totaled v).mp e) ▸ Finset.single_le_sum (f:=fun i=> v i) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)) (fun h=>p (bud_single v e j h))
def topStep (T:Tape.Table E n)(v w: Fin n→ Tape E)(Z:ℂ)(i:ℕ): ℂ:= Z* (T 1 (paused w))+∑ j, T 0 (update (paused w) j (v j i-w j i))
lemma treads (p:constantCoeff x=0)(q:constantCoeff y=0)(r:Ident i x y)(T:Tape.Table E n) (v w:Fin n→Tape E)(hz:i≠0)(hv:∀ j t,t< i→ v j t=w j t): coeff i (tabular (composed T x) v)-coeff i (tabular (composed T y) w)=topStep T v w (coeff i x-coeff i y) i:=by
    let x':= composed T x; let y':= composed T y; rw [tab_coeff,tab_coeff, ← Finset.sum_sub_distrib]; let U(j: Days n):= x' (j none) (rider v j)-y' (j none) (rider w j); let S(j:Option (Fin n)):= Finsupp.single j i; let K:= Finset.univ.image S; change ∑ j∈ tally i n, U j= _
    have hp: K ⊆ tally i n:= by intro v hv; obtain ⟨x,_,rfl⟩:= Finset.mem_image.mp hv; unfold S; rw [totaled]; simp
    have hu:Injective S:= by intro i' j' h; by_contra v; exact hz ((Finsupp.single_eq_same).symm.trans ((congr_arg (fun q:Normalize.Days n=> q i') h).trans (Finsupp.single_eq_of_ne v)))
    rw [← Finset.sum_subset hp, Finset.sum_image hu.injOn,Fintype.sum_option]; swap; · intro h v' w'; have he(k): h k< i:= bud_ne h v' k (fun p' => w' (p'.symm ▸ Finset.mem_image_of_mem S (Finset.mem_univ _))); unfold U; apply sub_eq_zero.mpr; rw [show x' (h none)=y' (h none) from comp_earlier r T (he none)]; exact congr_arg _ (funext fun j=>hv j (h (some j)) (he _))
    unfold topStep; congr 1
    · have he : rider v (S none)= paused w:= funext (fun j=>by unfold rider; rw [show S none (some j)=0 from Finsupp.single_eq_of_ne (by simp)]; exact hv j _ (Nat.pos_of_ne_zero hz)); have ht : rider w (S none)=paused w:= funext fun j=> by unfold rider; rw [show S none (some j)=0 from Finsupp.single_eq_of_ne (by simp)]; rfl
      unfold U; rw [he,ht]; rw [show S none none=i from Finsupp.single_eq_same]; unfold x' y'; rw [← _root_.sub_apply, compPriority T hz r p q, _root_.smul_apply]; rfl -- change norm solve singlenee
    apply Finset.sum_congr rfl; intro j _; have H(V:Fin n→Tape E): rider V (S (some j))=update (paused V) j (V j i):= by funext k; by_cases h:j=k <;> simp [rider,S,paused,h,Ne.symm]
    unfold U x' y'; rw [H,H,MultilinearMap.map_update_sub, show paused v=paused w from funext (fun j=>hv j _ (Nat.pos_of_ne_zero hz)), show S (some j) none=0 from Finsupp.single_eq_of_ne (by simp), comp_root p T,comp_root q T]
end split
end YM.SignedWilsonExpansion.Commission
