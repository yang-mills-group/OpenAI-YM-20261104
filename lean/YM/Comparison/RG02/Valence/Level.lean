import YM.Comparison.RG02.Assembly.Clipper
/-!
# Rank accounts for vacuum *and marked connected* kernels at one step

The rank charge used in this module has an ordinary polynomial-degree interpretation in the
rescaled fields (via continuous tensors); NOT an estimate on support, weight, gauge or locality.
Allows negative balances -- then the evaluated kernel vanishes, not an unconstrained constant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Valence
open Function Filter Finset YM.Analysis
open scoped Topology BigOperators Classical ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
structure Level (n : ℤ) (f : E→F) : Prop where
 smooth : ContDiff ℝ ω f
 high (i : ℕ) : n < i → ∀ x, iteratedFDeriv ℝ i f x=0
namespace Level
variable {n p : ℤ} {f g : E→F}
lemma jet (h : Level n f) (i : ℕ) (H : n < i) : Assembly.jet f i=0 := by
   ext x; unfold Assembly.jet; rw [h.high _ H 0]; simp
lemma negative (h : Level n f) (hn : n < 0) : f=0 := funext fun x=> by
   have hi:=h.high 0 (by omega) x; simpa only [iteratedFDeriv_zero_apply,Pi.zero_apply,_root_.zero_apply] using congrArg (fun T : YM.Tensor.T E F 0=> T (fun _=>x)) hi
lemma zero (n : ℤ): Level n (fun _ : E=> (0:F)):= ⟨contDiff_const,fun i _ x=> by simp⟩
lemma promote (h : Level n f) (he : n ≤ p) : Level p f := ⟨h.smooth,fun i hi => h.high i (lt_of_le_of_lt he hi)⟩
lemma down (h : Level n f) (v:E) : Level (n-1) (D v f):= by
   refine ⟨contDiff_iff_contDiffAt.mpr (fun x=> dSmooth h.smooth.contDiffAt _ (by simp)),fun i he x=>ContinuousMultilinearMap.ext fun l=>?_⟩
   rw [← Analysis.cons_inner ((h.smooth.of_le le_top).contDiffAt),h.high _ (by omega) x]; rfl
lemma up (hp : 0 ≤ n) (hf : ContDiff ℝ ω f) (h : ∀ v, Level (n-1) (D v f)) : Level n f:= by
   refine ⟨hf,fun i ht x=>?_⟩; cases i with
   | zero=>omega
   | succ i=>
     apply ContinuousMultilinearMap.ext; intro v
     nth_rw 1 [← Fin.cons_self_tail v]
     rw [Analysis.cons_inner (hf.of_le le_top|>.contDiffAt),(h _).high i (by omega)]; rfl
lemma add (h : Level n f) (he : Level n g) : Level n (fun v=> f v+g v):= by
   refine ⟨h.smooth.add he.smooth,fun i hi x=>?_⟩; rw [show (fun v:E=> f v+g v)=f+g from rfl,iteratedFDeriv_add_apply (h.smooth.contDiffAt.of_le le_top) (he.smooth.contDiffAt.of_le le_top), h.high i hi, he.high i hi,add_zero]
lemma total {T : Type*} {f : T→E→F} (t : Finset T) (h : ∀ i∈t,Level n (f i)) : Level n (fun x=>∑ i∈t,f i x):= by
   induction t using Finset.induction with
   | empty=> simp; exact Level.zero _
   | insert s t H IH=> simp_rw [sum_insert H]; apply (h s (mem_insert_self ..)).add; exact IH fun i hi=>h i (mem_insert_of_mem hi)
lemma constant (c : F) : Level 0 (fun _ : E=> c):= ⟨contDiff_const, fun i hi x=> congr_fun (iteratedFDeriv_const_of_ne (by omega : i ≠ 0) c) x⟩
lemma linear (C : E→L[ℝ] F) : Level 1 (⇑C):= by
   apply up zero_le_one C.contDiff; intro v; rw [sub_self,show D v ⇑C=fun _=> C v from funext fun a=>by rw [Analysis.D, ContinuousLinearMap.fderiv]]; exact constant _
section complex
variable {f g : E→ℂ}
lemma leisurely {f g : E→ℂ} (hf : Level n f) (hg : Level p g): ∀ (i : ℕ),n + p < i → ∀ x,iteratedFDeriv ℝ i (f*g) x=0 := by
   intro i; induction i generalizing n p f g
   case zero =>
      intro h x; cases show n < 0 ∨ p < 0 from by omega with
      | inl hl => rw [hf.negative hl,zero_mul]; exact (zero ..|>.high 0 h x)
      | inr hl => rw [hg.negative hl,mul_zero]; exact (zero ..|>.high 0 h x)
   case succ i IH =>
      intro h x; apply ContinuousMultilinearMap.ext; intro v
      have hi : D (v 0) (f*g)=D (v 0) f*g+f*D (v 0) g:= by
         ext1 a; simp only [D,fderiv_mul (hf.smooth.contDiffAt.differentiableAt (by simp)) (hg.smooth.contDiffAt.differentiableAt (by simp)), _root_.add_apply,_root_.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.add_apply]; ring
      nth_rw 1 [← Fin.cons_self_tail v]; rw [Analysis.cons_inner (f:=f*g) ((hf.smooth.mul hg.smooth).of_le le_top|>.contDiffAt),hi,iteratedFDeriv_add_apply (f:=D (v 0) f*g) (g:=f*D (v 0) g) (((hf.down _).smooth.mul hg.smooth).contDiffAt.of_le le_top) ((hf.smooth.mul (hg.down _).smooth).contDiffAt.of_le le_top), IH (hf.down _) hg (by omega), IH hf (hg.down _) (by omega),add_zero]; rfl
lemma mul (hf : Level n f) (hg : Level p g) : Level (n+p) (fun x=>f x*g x):= ⟨hf.smooth.mul hg.smooth,hf.leisurely hg⟩
lemma factor (hf : Level n f) (c : ℂ) : Level n (fun x=> c*f x):= by simpa only [zero_add] using (constant c).mul hf
end complex

lemma posted {r : ℕ} (h : Level r f) (x : E) : f x=∑ i∈range (r+1), Assembly.jet f i x := by
   induction r generalizing f x with
   | zero=>
     rw [zero_add,sum_range_one,Assembly.jet_zero]; symm
     let g(z:ℝ):= f (z•x); have he(z:ℝ): HasDerivAt g (D x f (z • x)) z := by exact (h.smooth.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt z (by simpa using (hasDerivAt_id' z).smul_const x)
     have ht(z:ℝ): HasDerivAt g 0 z := by simpa only [(h.down x).negative (by omega),Pi.zero_apply] using he z
     simpa [g] using is_const_of_deriv_eq_zero (fun z=>(ht z).differentiableAt) (fun z=>(ht z).deriv) 0 1
   | succ r IH =>
     have Hp : Level r (D x f) := by convert h.down x using 1; push_cast; ring
     let g(z:ℝ) := f (z•x)
     let e(z:ℝ) := ∑ i∈range (r+1+1), Assembly.jet f i (z•x)
     have he(z:ℝ): HasDerivAt g (D x f (z • x)) z := by exact (h.smooth.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt z (by simpa using (hasDerivAt_id' z).smul_const x)
     have hE(z:ℝ): HasDerivAt e (D x f (z•x)) z:= by
         unfold e; rw [show (D x f (z•x))=_ from IH Hp (z•x)]
         have hp (i:ℕ): HasDerivAt (fun t:ℝ=> Assembly.jet f (i+1) (t•x)) (Assembly.jet (D x f) i (z•x)) z := by simpa only [zero_add] using Assembly.Clipper.gradient h.smooth.contDiffAt (0:E) x z i
         simp_rw [sum_range_succ' _ (r+1), Assembly.jet_zero]; exact (HasDerivAt.fun_sum (fun i _ => hp i)).add_const _
     have hh := (IsOpen.eqOn_of_deriv_eq (x:=0) isOpen_univ isPreconnected_univ (fun u _=> (he u).differentiableAt.differentiableWithinAt) (fun u _=> (hE u).differentiableAt.differentiableWithinAt) (fun t _=> (he t).deriv.trans (hE t).deriv.symm) (Set.mem_univ 0) ?_) (Set.mem_univ 1)
     · simpa only [g,e,one_smul] using hh
     simp_rw [g,e,zero_smul,sum_range_succ' _ (r+1),Assembly.jet_zero,Assembly.Clipper.empty (_+1) (by omega) f,Finset.sum_const_zero,zero_add]

end Level
end YM.Comparison.RG02.Valence
