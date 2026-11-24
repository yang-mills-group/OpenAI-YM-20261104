import YM.AllOrder.Response.Algebra
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension.Series PositionX.Gauss Asymptotics
open scoped Topology ContDiff BigOperators Classical
abbrev Book (F:Type*) := ℕ→F→ℝ
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{P:ℝ→X} (hp:ContDiffAt ℝ ω P 0) {u v:Book X}{n k:ℕ}
def alters {X:Type*}(a b:Book X) : Book X:= Function.swap fun x=> plus (Function.swap a x) (Function.swap b x)
def wirings (f:X→ℝ):Book X:= Function.swap fun x=> just (f x)
def grass (P:ℝ→X)(u:Book X)(h:ℕ)(r:ℝ):=PositionX.Jet.delay (Function.swap u (P r)) h r
def weigh (P:ℝ→X)(u:Book X)(h:ℕ):ℝ:=∑ i∈Finset.range (h+1),someJ (u i ∘ P) (h-i)
def Budget (x:X)(u:Book X)(n:ℕ): Prop := ∀ i≤n,ContDiffAt ℝ ω (u i) x
variable (h:Budget (P 0) u n) (H:Budget (P 0) v n) {C : ℝ}
omit hp [NormedAddCommGroup X][NormedSpace ℝ X] in
lemma plus_real (u v:Book X)(x:X)(n:ℕ): alters u v n x=∑ i∈Finset.range (n+1), u i x * v (n-i) x:= by change plus _ _ n=_; rw [plus_sum]; exact Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> u i x*v j x) n -- Finset.Nat
omit hp in
lemma install_just (x:X){f:X→ℝ}(hg:ContDiffAt ℝ ω f x):Budget x (wirings f) n := by intro i _; by_cases hi:i=0; exact hi.symm ▸ hg; rw [show wirings f i= (fun _=>0) from funext fun _=> if_neg hi]; exact contDiffAt_const

omit hp in
lemma plus_in {x:X}(h:Budget x u n)(H:Budget x v n): Budget x (alters u v) n:=by
 intro i hi; rw [funext (fun z=> plus_real u v z i)]; apply ContDiffAt.sum; intro y hy; have hy:=Nat.le_of_lt_succ (Finset.mem_range.mp hy); exact (h _ (by omega)).mul (H _ (by omega))
include hp h
lemma studio : Act n (grass P u n) (weigh P u):=by
 let g(k:ℕ):=(fun x:ℝ=>x^k)*(u k ∘ P)
 have hg(k:ℕ)(he:k≤n):ContDiffAt ℝ ω (u k ∘ P) 0 := (h k he).comp _ hp
 have hh(k:ℕ)(he:k≤n):ContDiffAt ℝ ω (g k) 0:=(by fun_prop : ContDiffAt ℝ ω (fun x:ℝ=>x^k) 0).mul (hg k he)
 have hv:= exact_sum (F:=g) (range (n+1)) (fun i hi=>eo_Act n (hh i (Nat.le_of_lt_succ (mem_range.mp hi))))
 have ht : (∑ i ∈ Finset.range (n+1),g i) = grass P u n:=by ext1 x; rw [Finset.sum_apply]; rfl
 rw [ht] at hv; apply hv.repairs; intro k hk; rw [Finset.sum_apply,weigh]; symm
 calc _ = ∑ i∈Finset.range (k+1),someJ (g i) k:= Finset.sum_congr rfl (fun i hi=> (show _=someJ (g i) k from by have hi':i≤k:= Nat.le_of_lt_succ (mem_range.mp hi); rw [show g i= (fun t:ℝ=> t^i)*(u i∘ P) from rfl, jo_shift (hg i (hi'.trans hk)),if_pos hi']))
      _ = _ := Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun i hi hh=> (by rw [show g i=(fun t:ℝ=>t^i)*(u i ∘ P) from rfl,jo_shift (hg i (by simp only [mem_range] at hi; omega)),if_neg (by simpa only [Nat.lt_succ_iff.symm,mem_range] using hh)])
omit h in
lemma just_read {f:X→ℝ} (hg:ContDiffAt ℝ ω f (P 0)): weigh P (wirings f)=someJ (f ∘ P):= funext fun i=> (((studio hp (install_just _ (n:=i) hg)).repairs (b:=weigh P (wirings f)) (fun _ _=>rfl)).trans_at (by
 unfold grass delay; simp only [wirings,swap,just, smul_ite,smul_zero, sum_ite_eq', mem_range, pow_zero, one_smul]; simpa only [Nat.zero_lt_succ, if_true] using! eo_Act i (hg.comp (0:ℝ) hp)) le_rfl)
omit h hp in
lemma Budget.scale {x:X}{v:Book X}{C:ℝ}(h:Budget x v k):Budget x (C•v) k:=fun i hi=> contDiffAt_const.mul (h i hi) -- include?
lemma weigh_scale (hk:k≤n)(c:ℝ): weigh P (c•u) k=c*weigh P u k:= by
 unfold weigh; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; have hh: ContDiffAt ℝ ω (u i ∘ P) 0:=(h i ((Nat.le_of_lt_succ (mem_range.mp hi)).trans hk)).comp _ hp
 exact ((eo_Act (k-i) hh).smul c).writes _ le_rfl
include H
lemma weigh_add (hk:k≤n): weigh P (u+v) k=weigh P u k+weigh P v k:= by
 unfold weigh; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i hi=>?_); have hl : i≤n:=(Nat.le_of_lt_succ (mem_range.mp hi)).trans hk; exact congr_fun (some_add ((h _ hl).comp _ hp) ((H _ hl).comp _ hp)) _

-- evaluate product along grass; genuine `carry` infinite powers only Turn after installation. need nested later
omit hp h H [NormedAddCommGroup X][NormedSpace ℝ X] in
private lemma sum_T (a b:ℕ→ℝ→ℝ)(x:ℝ)(i:ℕ):
   x^i* ∑ j∈Finset.range (i+1),a j x*b (i-j) x= ∑ y∈ Finset.antidiagonal i,(x^y.1*a y.1 x) * (x^y.2*b y.2 x) := by
   rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>a i x*b j x) i,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k hk; rw [← Finset.mem_antidiagonal.mp hk,pow_add]; ring
omit hp h H [NormedAddCommGroup X][NormedSpace ℝ X] in
private lemma ledger (u v:Book X) (P:ℝ→X)(n:ℕ): (grass (P) u n)*(grass P v n) - grass P (alters u v) n = ∑ p∈((((Finset.range (n+1))×ˢ Finset.range (n+1))).filter (fun p:ℕ×ℕ=> n<p.1+p.2)), fun t => t^(p.1+p.2)*(u p.1 (P t)*v p.2 (P t)):= by
 funext x; unfold grass PositionX.Jet.delay Function.swap; simp only [Pi.sub_apply,Pi.mul_apply, smul_eq_mul, plus_real,Finset.sum_apply]
 let Z:=Finset.range (n+1)
 let F (p:ℕ×ℕ):=x^p.1*u p.1 (P x)*(x^p.2*v p.2 (P x)); let A:= Z ×ˢ Z
 have hg(p): F p=x^(p.1+p.2)*(u p.1 (P x)*v p.2 (P x)):=by unfold F; rw [pow_add]; ring
 have hh : ∑ p∈A,F p= _:= Finset.sum_product _ _ F -- ?? uncurrying
 have ha : (∑ i∈Z,∑ y∈Finset.antidiagonal i,F y) =∑ i∈A.filter (fun p=>p.1+p.2≤n), F i:=by
    rw [← Finset.sum_biUnion]; congr 1
    · ext ⟨i,j⟩; simp [A,Z]; omega
    · intro i hi j hj he; exact Finset.disjoint_left.mpr fun k h1 h2=>he ((Finset.mem_antidiagonal.mp h1).symm.trans (Finset.mem_antidiagonal.mp h2))
 apply (sub_eq_iff_eq_add).mpr
 calc _ = ∑ i∈A, F i:= by rw [hh]; simp_rw [Finset.sum_mul,Finset.mul_sum]; rfl -- edit
      _ = _ := by
                simp_rw [show ∀ i:ℕ, x^i*(∑ j∈Finset.range (i+1), u j (P x)*v (i-j) (P x))= ∑ y∈Finset.antidiagonal i,F y from fun i=> sum_T (fun i _=>u i (P x)) (fun i _=> v i (P x)) x i, ← hg]
                change _=_+(∑ i ∈ Z, ∑ j∈_,_);
                rw [ha,add_comm,← Finset.sum_filter_add_sum_filter_not A (fun p:ℕ×ℕ=>p.1+p.2≤n) F] -- occ edit
                simp only [not_le]; rfl
lemma weigh_mul (hk:k≤n): weigh P (alters u v) k= plus (weigh P u) (weigh P v) k:= by
 let g := grass P (alters u v) n; let f:=(grass P u n) * (grass P v n)
 have ht:= exact_prod (studio hp h) (studio hp H); have hh:= studio hp (plus_in h H)
 have hv:someJ (f-g) k=0:= by
   let s:= ((Finset.range (n+1))×ˢ Finset.range (n+1)).filter (fun p:ℕ×ℕ=> n<p.1+p.2)
   let F (p : ℕ×ℕ):= (u p.1 ∘ P) * (v p.2 ∘ P); let G(p:ℕ×ℕ):=(fun t:ℝ=> t^(p.1+p.2))*F p
   have hh (i:ℕ×ℕ) (he:i∈s): i.1≤n ∧ i.2≤n ∧ k < i.1+i.2:= by simp only [s,Finset.mem_filter, Finset.mem_product, Finset.mem_range] at he; omega
   have hF i (hx:i∈s):ContDiffAt ℝ ω (F i) 0:= ((h _ (hh i hx).1).comp _ hp).mul ((H _ (hh i hx).2.1).comp _ hp)
   rw [show f-g=∑ i∈s,G i from ledger u v P n, (exact_sum s (fun i hi=> eo_Act k (show ContDiffAt ℝ ω (G i) 0 from (contDiffAt_id.pow (i.1+i.2)).mul (hF i hi)))).writes _ le_rfl,Finset.sum_apply]; refine Finset.sum_eq_zero fun i hi=>?_ ; rw [show G i= _ from (rfl : G i=(fun t:ℝ=> t^(i.1+i.2))*F i), jo_shift (hF i hi), if_neg ((hh i hi).2.2.not_ge)]
 rw [←ht.writes k hk, ←hh.writes k hk]; rw [some_sub (show ContDiffAt ℝ ω f 0 from ht.nice) (show ContDiffAt ℝ ω g 0 from hh.nice),Pi.sub_apply] at hv; exact (sub_eq_zero.mp hv).symm
end YM.AllOrder.Response
