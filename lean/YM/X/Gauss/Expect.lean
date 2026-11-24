import YM.X.Gauss.Plausible
import YM.Next.RANK.Common
/-!
One-loop Gaussian pushforward by cut and IBP for arbitrary finite monomial sums on potentials. Avoid determinant gauge mixing at this order.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gauss
open Function Filter Set MeasureTheory PertExtension PertExtension.GaussianScore
open scoped BigOperators Topology ContDiff Classical
variable {E F J : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (P:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
local notation "E₁"=>P.average μ
variable {f g:E→ℝ}(hf:Plausible f)(hg:Plausible g){a:J→E→ℝ}
lemma average_const (c:ℝ): E₁ (fun _=> c)=c:= by
   have he := Law.empty P μ; unfold Law.average at *
   change ((∫ x:E,c * P.kern x ∂μ)/_)=_
   rw [integral_const_mul,mul_div_assoc];rw [one_mul] at he; rw [he,mul_one]
lemma average_scale (c:ℝ) (f:E→ℝ): E₁ (c • f)= c*(E₁ f):= by unfold Law.average; rw [smul_mul_assoc c f]; simp_rw [Pi.smul_apply,MeasureTheory.integral_smul]; exact mul_div_assoc .. -- wrong dir?
lemma average_add (hf:Plausible f)(hg:Plausible g): E₁ (f+g)= E₁ f+E₁ g:= by unfold Law.average; rw [add_mul]; simp_rw [Pi.add_apply,MeasureTheory.integral_add (P.integrable_entry μ hf.invoice hf.smooth.continuous) (P.integrable_entry μ hg.invoice hg.smooth.continuous),add_div]
lemma average_sub (hf:Plausible f)(hg:Plausible g): E₁ (f-g)= E₁ f-E₁ g:= by unfold Law.average; rw [sub_mul]; simp_rw [Pi.sub_apply,MeasureTheory.integral_sub (P.integrable_entry μ hf.invoice hf.smooth.continuous) (P.integrable_entry μ hg.invoice hg.smooth.continuous),sub_div]
lemma average_sum {k:Finset J}(h:∀ i∈k,Plausible (a i)): E₁ (∑ i∈k,a i)= ∑ i∈k,E₁ (a i):= by
   induction k using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact average_const ..
   | insert i s hi ih=> simp_rw [Finset.sum_insert hi, average_add P μ (h i (by simp)) (Plausible.sum (k:=s) fun j hj=> h j (by simp [hj]))]; congr 1; apply ih; intro j hj; exact h j (by simp [hj])
lemma byParts (hf:Plausible f)(v:E): E₁ (diff' v f)= E₁ (f* (⇑(P.P v))):= by
   rw [← sub_eq_zero, ←average_sub _ _ (hf.ds _) (hf.mul (Plausible.line _))]; unfold Law.average 
   have hi : ∀ (x:E) (t:ℝ), HasDerivAt (fun r:ℝ=> f (x+r • v)) (diff' v f (x+t • v)) t:= fun x t=> by exact ((hf.smooth.differentiable (by simp) (x+t • v)).hasFDerivAt).comp_hasDerivAt t (show HasDerivAt (fun r:ℝ=> x+r • v) v t from (by simpa only [one_smul] using (((hasDerivAt_id' t).smul_const v).const_add x)))
   have he:= P.translation_lemma v hf.invoice hf.smooth.continuous (hf.ds v).invoice (hf.ds v).smooth.continuous hi μ; rw [he,zero_div]
-- projection Gaussian keeps law, structural induction augmented by derivative congruence property (times f a requires knowing derivative of f separately; use span incl all derivs via induction degree?)
-- use all product index monomials; induct list recursively using `recursion`; need to apply IH at derivative-of-each excluding. use Plausible→span glyph normalized.
variable (Q:Law F) (ν:Measure F)[ν.IsAddHaarMeasure]
variable (T:E→ₗ[ℝ] F)(H:∀ (v:Module.Dual ℝ F),T (P.inverse (v.comp T))=Q.inverse v)
local notation "E₂"=>Q.average ν
@[simp] lemma average_zero : E₁ 0=0 := average_const ..
-- use structural induction recursion via alternative lemma `Pla degree`: prove equality for product p multiplying list? or use rename into common Wick polynomial. reuse glyph_overlap clone general and polynomial.cont. need symmetry for later.

open Next.Rank Next.Rank.Normal MvPolynomial
variable (S:J→Module.Dual ℝ E)
def formed (P : Law E) : Symmetric J:= ⟨fun i j=> (P.wick (S i) (S j):ℂ),fun i j=> by congr 1; exact (by unfold Law.wick; rw [← show P.P (P.inverse (S i))= S i from P.applies _,← show P.P (P.inverse (S j))= S j from P.applies _,Law.solves,Law.solves, Law.turns])⟩
lemma glyph (A : Type*) [Fintype A](f:A→J)(s:Finset A):
  (↑(E₁ (Law.product (S ∘ f) s)):ℂ)=blend (formed S P) 0 (glyphs f s):= by
     induction s using Finset.strongInduction with
     | _ s ih=>
       obtain rfl|⟨i,hi⟩:=s.eq_empty_or_nonempty
       · simp [Law.product, show (Law.product _ ∅)=1 from rfl,Law.empty,glyphs,average_const]
       have hv : Law.product (S ∘ f) s=(fun x=> Law.product (S ∘ f) (s.erase i) x*S (f i) x):=funext fun x=> (Finset.prod_erase_mul _ _ hi).symm
       have he:= (P.recursion μ (S (f i)) (S ∘ f) (s.erase i)); rw [hv, he]
       conv_rhs=> rw [← Finset.insert_erase hi]
       rw [Normal.spring 0 (formed ..) f (s.erase i) (Finset.notMem_erase i s),Pi.zero_apply,zero_mul,zero_add]
       rw [Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro j hj; rw [Complex.ofReal_mul,mul_comm]; exact congr_arg₂ (·*·) rfl (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) (Finset.erase_ssubset hi)))
private def mono (E : Type*)[NormedAddCommGroup E][NormedSpace ℝ E] : Submodule ℝ (E→ℝ):= Submodule.span ℝ (⋃ i:ℕ, Set.range (fun a:Fin i → Module.Dual ℝ E=> Law.product a Finset.univ))
-- easier prove equality for all pl via f:MvPolynomial; introduce `deconstruct` there
end YM.PositionX.Gauss
