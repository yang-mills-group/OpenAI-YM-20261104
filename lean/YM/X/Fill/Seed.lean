import YM.X.Fill.Stones
/-!
# Mark-shell integral of singular singleton. Specialized class (can include dummy powers). Formation and use.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Friend
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Fielding Haze Clove Interval CellsInt Shelf Size Print
open scoped Topology ContDiff Classical BigOperators
variable {q:ℕ+} (hq:1<q.val){k m:ℕ}{a b n : ℤ}{R r:ℝ}
local notation "ε"=>epsilon q
variable {f g:Mist ℂ}
def seed (q:ℕ+)(r:ℝ)(h:ℤ): Submodule ℂ (Mist ℂ):= Submodule.span ℂ {p|∃ (f:Mist ℂ) (m:ℕ)(w:GridF), Chase q r (h-(2+m)) f ∧ w∈bird m ∧ p=f*squall q w}
lemma seeded (F:GridF)(f: Mist ℂ)(h:F∈bird k)(p:Chase q r (n-(2+k)) f): f*squall q F∈seed q r n:= Submodule.subset_span ⟨f,k,F,p,h,rfl⟩
include hq
lemma fewer(h:f∈seed q r a)(hy:b≤a): f∈seed q r b:= by
    apply (show seed q r a≤ seed q r b from ?_) h; apply Submodule.span_le.mpr; rintro _ ⟨f,m,w,p,h,rfl⟩; exact seeded _ _ h (p.falls hq (by omega))
lemma fed (h:f∈seed q r a)(hp:Chase q r b g): f*g∈seed q r (a+b):= by
    induction h using Submodule.span_induction with
    | mem i hi=> obtain ⟨f,m,w,h,p,rfl⟩:=hi; rw [mul_right_comm]; refine seeded _ _ p (Chase.falls hq (h.mulC hq hp) ?_); omega
    | zero=> simp
    | add a b _ _ y x=> rw [add_mul]; exact Submodule.add_mem _ y x
    | smul a b _ x=> rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ x
variable (φ:Floor R) (hr:R<r)
local notation "Θ"=> Floor.maskL q φ
omit hq
lemma influx_plus (p:ℕ→Lane)(f g:Mist ℂ): influx p (f+g)= influx p f+ influx p g:= funext (fun i=> bead_add ..)
lemma influx_smul (p: ℕ→Lane)(f:Mist ℂ)(c:ℕ→ℝ): influx p (fun i z=> c i • f i z) = c • influx p f:= by ext1 i; change influx p _ i = c i • influx p f i; unfold influx beadR; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun x _=> smul_comm ..
lemma incomes (p:ℕ→ Lane)(f:Mist ℂ)(c:ℕ→ℂ): influx p (fun i z=>c i • f i z) = c • influx p f:= by ext1 i; change influx p _ i = c i • influx p f i; unfold influx beadR; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum]; refine Finset.sum_congr rfl fun x _=> smul_comm ..
lemma inflowed (p:ℕ→Lane)(f g:Mist ℂ): influx p (f*g)= notZero (fun i=>cane (p i) (f i)) g:= by
    ext1 k; set m:= cane (p k) (f k); let s:= (p k).support; let z:= (fun x=>m x*g k x); have h(x:Cover): p k x • (f k x*g k x)=z x:= by unfold z m;rw [cane_at, smul_mul_assoc];
    change (∑ x∈s,p k x • (_ * _))=(∑ x∈m.support,z x); simp_rw [h]; symm; refine Finset.sum_subset ?_ ?_
    · intro x hx; have ht:(p k) x • (f k x)≠0:= Finsupp.mem_support_iff.mp hx; exact Finsupp.mem_support_iff.mpr (fun he=>ht (he ▸ zero_smul ..))
    intro x hx ht; unfold z; rw [Finsupp.notMem_support_iff.mp ht,zero_mul]
include hq hr
lemma onceG (h: Chase q r (4-(2+k)) f) (B:GridF)(hp:B∈bird k): Released (influx Θ (f*squall q B)):= by
    induction hp using Submodule.span_induction with
    | mem i hi=>
       obtain ⟨l,rfl,v,rfl⟩:=hi; -- fixes k
       let p(i):= cane (Θ i) (f i);
       have he : Chase q r (4-(2+l.length)) (palm p):= by
          let g:= Haze.relabel Θ;
          have hp:= (Chase.fore (w:=φ) (r:=r) hq).com.mulC hq h; rw [zero_add] at hp; exact hp
       rw [inflowed]; apply stargem hq l v _ φ.positive.le hr he; exact star_smul _ (φ.onboard hq) -- infer
    | zero=>
       rw [show squall q 0=0 by ext1; ext1; simp [squall],mul_zero,show influx Θ 0=(0:ℕ→ℂ) from ?_]; exact Released.zero
       ext1; simp [influx,beadR,Finsupp.linearCombination_apply,Finsupp.sum]
    | add a b _ _ x y=>
       rw [show squall q (a+b)=squall q a+squall q b from funext (fun i=>funext (fun z=> Complex.ofReal_add ..)), mul_add,influx_plus]; exact x.add y
    | smul a i _ h=>
       rw [show f*squall q (a • i)=(fun b p=> a • (f*squall q i) b p) from ?_, influx_smul]; exact h.smul (a:=fun i:ℕ=>a) ⟨a,tendsto_const_nhds⟩
       ext1 b; ext1 z; change f b z * ↑(a*i _ _ _) = a • (f b z * _); rw [Complex.ofReal_mul, Complex.real_smul]; unfold squall; ring -- coercion squall
lemma seed_rise (h: f∈seed q r 4): Released (influx Θ f):= by
   induction h using Submodule.span_induction with
   | mem x h=> obtain ⟨f,n,x,h,hx,rfl⟩:=h; exact onceG hq φ hr h x hx
   | zero=> rw [show influx (V:=ℂ) Θ 0=(0:ℕ→ℂ) from by ext1; simp [influx,beadR,Finsupp.linearCombination_apply,Finsupp.sum]]; exact Released.zero
   | add a b _ _ x y=> rw [influx_plus]; exact x.add y
   | smul a b _ h=> have he:= incomes Θ b (fun i:ℕ=>a); change influx Θ (a • b)= _ at he; rw [he]; exact Shelf.breaths (constell a) h
end YM.PositionX.Friend
