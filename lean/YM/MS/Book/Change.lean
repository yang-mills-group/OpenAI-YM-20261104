import YM.MS.Book.LogPS
/-! Dependence on the lower order Plan. Annihilator of changes. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Convolve Logarithm -- trim
open PowerSeries (coeff)
variable {I:Type} {P: Type}[AddCommGroup P][Module ℂ P] {a b c d:Cn} {n m:ℕ}

def Rem (c d:Cn)(n:ℕ):=∀ i,i≤n→ coeff i c=coeff i d
def Preset (c d:Cn)(n:ℕ):=∀ i,i<n→ coeff i c=coeff i d
lemma compose_mul (hc:Rem c d n)(ha:Rem a b n): Rem (c*a) (d*b) n:= by
    intro i hi; rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]; apply Finset.sum_congr rfl; intro j hj; obtain hp:=mem_antidiagonal.mp hj; rw [hc _ (by omega),ha _ (by omega)]
lemma compose_power (hc:Rem c d n)(j:ℕ): Rem (c^j) (d^j) n:= by induction j with| zero=>rw [pow_zero,pow_zero]; exact fun i hi=>rfl| succ j ih=> simpa [pow_succ] using compose_mul ih hc
lemma tickets (hc:Rem c d n) : Rem (PowerSeries.invOfUnit c 1) (PowerSeries.invOfUnit d 1) n:= by
    intro i; induction i using Nat.strong_induction_on with
    | _ i ih=>
        intro hi; rw [PowerSeries.coeff_invOfUnit,PowerSeries.coeff_invOfUnit];
        split; swap; · congr! 1; refine Finset.sum_congr rfl fun k hk=>?_; split <;> rename_i hx <;> (try rfl); rw [ih _ hx (by omega),hc _ (by obtain h:=mem_antidiagonal.mp hk; omega)]
        rfl
lemma compositeList {V W:I→Cn}(h:∀ i,Rem (V i) (W i) n)(l:List I): Rem ((l.map V).prod) ((l.map W).prod) n:= by
    induction l with| nil=>exact fun i hi=>rfl| cons i l ih=> exact compose_mul (h i) ih
lemma sub_alt {F:T P}(h: Rem c d n): substitute c F n=substitute d F n:=by
    rw [rules,rules]; exact Finset.sum_congr rfl fun i hi=> by rw [cut,cut,compose_power h _ _ (le_refl n)]

section op
variable (hr:0<n)
lemma next_pair (he:Preset a b n)(hh:Preset c d n) (hv:0< n): coeff n (b*d)-coeff n (a*c)=(coeff n b-coeff n a)*coeff 0 c+coeff 0 a*(coeff n d-coeff n c):=by
   let J:=antidiagonal n; have h1:(n,0)∈J:=mem_antidiagonal.mpr (by simp); have h2:(0,n)∈J:=mem_antidiagonal.mpr (by simp); let F (i:ℕ×ℕ):= coeff i.1 b*coeff i.2 d-coeff i.1 a *coeff i.2 c
   simp_rw [PowerSeries.coeff_mul,← Finset.sum_sub_distrib]; change ∑ i∈J,F i=_; rw [← Finset.add_sum_erase _ F h1, ← Finset.add_sum_erase _ F (by exact Finset.mem_erase.mpr ⟨show (0,n)≠(n,0) by rintro he; have h := congr_arg Prod.fst he; have := congr_arg Prod.snd he; simp at *; omega,h2⟩),Finset.sum_eq_zero ?u]; swap -- hm order mem_erase orientation
   · rintro ⟨a,b⟩ h'; simp only [Finset.mem_erase, J, Finset.mem_antidiagonal] at h'; obtain ⟨h1,h2,hl⟩:=h'; replace h1:=show ¬(a=0 ∧ b=n) from fun h=> h1 (Prod.ext h.1 h.2); replace h2:=show ¬(a=n∧ b=0) from fun h=>h2 (Prod.ext h.1 h.2); unfold F; dsimp only; rw [he a (by omega), hh b (by omega), sub_self]
   unfold F; simp only; rw [he _ hv,hh _ hv]; ring
-- extractor of coupling: only R=1 term survives when deeper changes.
lemma only_one (F:T P)(h:Preset c d n)(hx:Rooted c)(hv:0<n): substitute d F n= substitute c F n+ (coeff n d -coeff n c) • F 1:= by
   rw [rules,rules, ← sub_eq_iff_eq_add'] -- check
   rw [← Finset.sum_sub_distrib,Finset.sum_eq_single 1,cut,cut,pow_one,pow_one,sub_smul]
   · intro i hi hJ; rcases i with _|k; · simp [cut]
     unfold cut; rw [pow_succ,pow_succ,← sub_smul]; have hu:k≠0:=by omega
     rw [next_pair (a:=c^k) (b:=d^k) (fun i hi=> compose_power (n:=i) (fun j hj=>h _ (by omega)) k _ (le_refl i)) h hv,hx,show coeff 0 (c^k)=0 from blocked hx (by omega)]; simp
   exact fun h=> (h (Finset.mem_Iic.mpr hv)).elim
end op
end YM.MS.Book.Program
