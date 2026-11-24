import YM.OPE.Compatible.Ash.Hush
/-!
# Power algebra
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{k j m:ℕ}{f g:ℕ→ℝ}{x y:ℝ}
def Marble (U:Gloam)(k:ℕ)(f:ℕ→ℝ):Prop:=∃ a, Sake U k (f-billX U a k)
lemma Sake.dark (hf:Sake U k f):Sake U k (-f):=by obtain ⟨A,HA,H⟩:=hf; exact ⟨A,HA,fun i=> by simpa using H i⟩
lemma Sake.pen (hf:Sake U k f)(hg:Sake U j g):Sake U (k+j) (f*g):=by
    obtain ⟨A,hA,H⟩:=hf; obtain ⟨B,hB,L⟩:=hg; refine ⟨A*B,by positivity,fun i=>?_⟩; rw [Pi.mul_apply,norm_mul,pow_add]; have ht:=mul_le_mul (H i) (L i) (norm_nonneg _) (by have h:=U.h_pos i; positivity); exact ht.trans (le_of_eq (by ring))
lemma sake_one (U:Gloam)(x:ℝ):Sake U 0 (fun _=>x):=⟨‖x‖,norm_nonneg _,fun i=>by rw [pow_zero,mul_one]⟩
lemma coral_pay (U:Gloam)(x:ℝ)(j:ℕ): Sake U j (coral U j x):=by
   refine ⟨‖x‖,by positivity,fun i=>?_⟩; rw [coral,norm_smul,Real.norm_of_nonneg (pow_nonneg (U.h_pos _).le _),mul_comm]
lemma Marble.make (hf:Sake U k f):Marble U k f:=⟨0,by rw [show billX U (0:ℕ→ℝ) k=(0:ℕ→ℝ) from funext fun i=>by simp [billX,coral],sub_zero]; exact hf⟩
lemma Marble.sum (hf:Marble U k f)(hg:Marble U k g):Marble U k (f+g):=by
    obtain ⟨a,h⟩:=hf; obtain ⟨b,h'⟩:=hg; refine ⟨a+b,?_⟩; rw [show (billX U (a+b) k)=(billX U a k)+(billX U b k) from funext fun j=>by simp only [billX, Pi.add_apply,coral,smul_add,Finset.sum_add_distrib],show f+g-(billX U a k+billX U b k)= (f-billX U a k)+(g-billX U b k) from by abel]; exact h.fuse h'
lemma Marble.term (U:Gloam)(x:ℝ)(j k:ℕ):Marble U k (coral U j x):=by
    by_cases h:j<k
    · refine ⟨Pi.single j x,?_⟩; rw [show billX U (Pi.single j x) k=coral U j x from funext fun i=>?_,sub_self]; exact sake_zero ..
      unfold billX; rw [Finset.sum_eq_single j, Pi.single_eq_same]; intro b _ bh; rw [Pi.single_eq_of_ne bh]; simp [coral]; exact fun x=>(x (Finset.mem_range.mpr h)).elim -- parse
    exact Marble.make ((coral_pay ..).down (not_lt.mp h))
lemma Cleared.coralX:Cleared U (coral U j x):=fun _ _=> Marble.term ..
lemma Marble.line {E:Type*}(t:Finset E)(a:E→ℕ→ℝ)(h:∀ i∈t,Marble U k (a i)):Marble U k (∑ i∈t,a i):=by
   induction t using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact Marble.make (sake_zero ..)
   | insert e t he ih=> rw [Finset.sum_insert he]; exact (h _ (Finset.mem_insert_self ..)).sum (ih (fun _ hp=> h _ (Finset.mem_insert_of_mem hp)))
lemma billc (U:Gloam)(f:ℕ→ℝ)(j:ℕ): billX U f j=∑ b∈ Finset.range j,coral U b (f b):=by funext i; rw [Finset.sum_apply];rfl
lemma Cleared.bill {U:Gloam}:Cleared U (billX U f j):=by rw [billc]; exact Cleared.tally _ _ (fun _ _=>Cleared.coralX)
lemma Marble.pen (hf:Marble U k f)(hg:Marble U k g):Marble U k (f*g):=by
   obtain ⟨a,h⟩:=hf; obtain ⟨b,K⟩:=hg; let A:=billX U a k; let B:=billX U b k; change Sake U k (f-A) at h; change Sake U k (g-B) at K
   have hc:Sake U 0 A:=Cleared.bill.cost; have hd:Sake U 0 B:=Cleared.bill.cost; have he:Sake U 0 g:=by rw [show g=(g-B)+B from by abel]; exact (K.down (by omega)).fuse hd
   have hp:Marble U k (A*B):=by
       unfold A B; simp_rw [billc,Finset.sum_mul, Finset.mul_sum]; apply Marble.line; intro i _; apply Marble.line; intro j _; rw [show coral U i (a i)*coral U j (b j)=coral U (i+j) (a i*b j) from funext fun x=>by simp only[Pi.mul_apply,coral,pow_add, smul_eq_mul];ring]; exact Marble.term ..
   rw [show f*g=A*B+(f-A)*g+(g-B)*A from by ring]; exact (hp.sum (Marble.make (h.pen he))).sum (Marble.make (K.pen hc)) -- k+0 defeq
lemma Cleared.pen (hf:Cleared U f)(hg:Cleared U g):Cleared U (f*g):=fun i hi=> Marble.pen (hf i hi) (hg i hi)
-- If a shift h^n occurs
lemma Sake.clean (h:Sake U 0 f):Marble U 0 f:=Marble.make h
def Bloom (U:Gloam)(k:ℕ)(f:ℕ→ℝ) (x:ℝ):Prop:= Sake U k f ∧ Cleared U (fun i=>(U.h i^k)⁻¹*f i) ∧ Tendsto (fun i=>(U.h i^k)⁻¹*f i) atTop (𝓝 x)
lemma flourish (hf:Cleared U f):∃ c:ℝ,Tendsto f atTop (𝓝 c):=by
   obtain ⟨a,h⟩:=hf 1 zero_lt_one; refine ⟨a 0,?_⟩; have he:=h.flop (by norm_num : 0<1); have h':=he.add (van a (U:=U) (m:=0)); rwa [show (fun i=>(f-billX U a 1) i+billX U a (0+1) i)=f from funext fun i=>sub_add_cancel .., zero_add] at h'
lemma fromCore (h:Cleared U (fun i=>(U.h i^k)⁻¹*f i)):∃ x,Bloom U k f x:=by
   let g:=fun i=>(U.h i^k)⁻¹*f i; obtain ⟨x,hx⟩:=flourish h; refine ⟨x,?_,h,hx⟩; have he: f=coral U k (1:ℝ)*g:=by funext i; simp only [Pi.mul_apply,g,coral,smul_eq_mul, mul_one]; have hp:=U.h_pos i; field_simp
   rw [he]; exact (coral_pay ..).pen h.cost
lemma Bloom.pen (h:Bloom U k f x)(he: Bloom U j g y):Bloom U (k+j) (f*g) (x*y):=by -- y binder
    let F:=fun i=>(U.h i^k)⁻¹*f i; let G:=fun i=>(U.h i^j)⁻¹*g i; refine ⟨h.1.pen he.1,?_⟩; rw [show (fun i=>(U.h i^(k+j))⁻¹*(f*g) i)= F*G from funext fun x=>by simp only [Pi.mul_apply,pow_add,F,G,mul_inv]; ring]; exact ⟨Cleared.pen h.2.1 he.2.1,h.2.2.mul he.2.2⟩
lemma Bloom.full (h:Bloom U k f x):Cleared U f:=by
   let F:=fun i=>(U.h i^k)⁻¹*f i; have he:F*(coral U k (1:ℝ))= f:=by funext i; simp only [Pi.mul_apply,F,coral,smul_eq_mul,mul_one]; have hp:=U.h_pos i;field_simp
   rw [←he]; exact Cleared.pen h.2.1 Cleared.coralX
end YM.OPE.Balsam
