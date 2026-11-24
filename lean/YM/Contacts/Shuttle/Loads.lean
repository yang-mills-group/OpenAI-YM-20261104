import YM.Contacts.Barrage.Trophy
/-!
Mark rooted cylinders. Probe address transport not implicit in this type;
payment here for *each* weighted mark query. Programs will certify connections
on this genuine lattice alphabet, not assuming continuous-motion estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine
open Milling Milling.Steam Milling.Forge Milling.Garf
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {G : Gauge}{X Y ι κ α β V E : Type}{n h : ℕ}{b c:ℝ}{s t:ℝ≥0}
variable [Fintype ι][NormedAddCommGroup E]
def fee (l:Pulse.Range X)(o:X)(x:ι→X) := l.bill (fun i:Option ι => i.elim o x)
def Rest (l:Pulse.Range X)(o:X)(f:(ι→X)→E)(b:ℝ): Prop := SumBudget (fun x=> ‖f x‖ * fee l o x) b
variable {l: Pulse.Range X}{o:X}
lemma fee_one (x:ι→X): 1≤ fee l o x:= l.one_bill _
lemma fee_plus (x:ι→X):0 ≤ fee l o x:= zero_le_one.trans (fee_one _)
lemma fee_leg (x:ι→X)(i:ι): l.step o (x i) ≤ fee l o x := l.width (fun i:Option ι =>i.elim o x) none (some i)
lemma fee_basis (x:Fin n→X): fee l o x=l.bill (Fin.cons o x):= by
   rw [fee,← l.retrieve (finSuccEquiv n) _ (finSuccEquiv n).surjective]; congr! 2; funext i; refine Fin.cases ?_ (fun i=>?_) i <;> simp [Function.comp]
variable {F Q:(ι→X)→E}{f g:Field ι X}
namespace Rest
lemma cash (h:Rest l o F b): 0≤b:= budget_nonneg h
lemma upto (f:Pulse.Range X)(hf:∀ i:Option ι→X,f.bill i ≤ l.bill i) (hc:b≤c)(h:Rest l o F b): Rest f o F c:= budget_loosen (budget_mono h (fun i=> mul_nonneg (norm_nonneg _) (fee_plus i)) (fun i=> mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _))) hc -- unused binders
lemma ist (h:Rest l o F b) (hc : b≤c): Rest l o F c:= budget_loosen h hc
lemma add (h:Rest l o F b)(hg: Rest l o Q c): Rest l o (F+Q) (b+c):= budget_mono (budget_plus h hg) (fun i=> mul_nonneg (norm_nonneg _) (fee_plus i)) (fun i=> by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (norm_add_le ..) (fee_plus i))
lemma smul [NormedSpace ℝ E](h:Rest l o F b)(a:ℝ): Rest l o (a • F) (‖a‖*b):= by
    simpa only [Rest,Pi.smul_apply,norm_smul,mul_assoc] using budget_scale (norm_nonneg a) h
lemma zero : Rest l o (fun _ : ι→X=> (0:E)) 0 := by simpa only [Rest,norm_zero,zero_mul] using (budget_zero (α:=ι→X))
lemma sub (h:Rest l o F b)(hg:Rest l o Q c): Rest l o (F-Q) (b+c):= budget_mono (budget_plus h hg) (fun i=> mul_nonneg (norm_nonneg _) (fee_plus i)) (fun i=> by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (norm_sub_le ..) (fee_plus i))
lemma sum {u:Finset κ}{F:κ→ (ι→X)→E}{b:κ→ℝ}(h:∀ i∈u,Rest l o (F i) (b i)): Rest l o (∑ i∈u,F i) (∑ i∈u,b i):= by
   simp_rw [Rest,Finset.sum_apply]; exact budget_collect fee_plus h
lemma raw (h: Rest l o F b): SumBudget (fun i=> ‖F i‖) b:= budget_mono h (fun i=>norm_nonneg _) (fun i=> le_mul_of_one_le_right (norm_nonneg _) (fee_one i))
lemma summ [CompleteSpace E](h:Rest l o F b): Summable F:= (h.raw.2.1).of_norm
-- watching an orthogonal direction: must avoid requiring nonempty i.
lemma points {u: (ι→X)→ℝ}(hu:∀ i,‖u i‖ ≤ c * fee l o i)(hc:0≤c)(h:Rest l o f b): SumBudget (fun i=> ‖f i*u i‖) (c*b) := by
    apply budget_mono (budget_scale hc h) (fun _=> norm_nonneg _)
    intro i; rw [norm_mul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (hu i) (norm_nonneg _)
end Rest
def hinge (p:X→Y)(v:ι→X) := p∘v
def packing (p:X→Y)(f:Field ι X): Field ι Y:= cram (hinge (ι:=ι) p) f
def say (f:Field ι X) (V:ι→ X→ℝ) := ∑' i,f i * ∏ j,V j (i j)
lemma haul {p:X→Y}(w: (ι→Y)→ℝ) (h: Summable (fun i=> f i * w (hinge p i))): ∑' j, packing p f j * w j=∑' i,f i * w (hinge p i) := by
   convert (heavy (hinge p (ι:=ι)) h).tsum_eq using 1; apply tsum_congr; intro j; unfold packing cram; rw [←tsum_mul_right]; exact tsum_congr fun i=> congr_arg (fun j=> f i.val * w j) i.property.symm
lemma hauled {p:X→Y} [Fintype Y](hv:Summable f) (w:(ι→Y)→ℝ): ∑ v,packing p f v * w v=∑' i,f i*w (hinge p i):= by
   rw [← tsum_fintype (L:=.unconditional _)]; apply haul; have hw y: ‖w y‖ ≤ ∑ i:ι→Y, ‖w i‖:= single_le_sum (s:=univ) (fun _ _=>norm_nonneg _) (mem_univ _)
   exact Summable.of_norm ((hv.norm.mul_right _).of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> (norm_mul ..).le.trans (mul_le_mul_of_nonneg_left (hw _) (norm_nonneg _)))) -- hv.norm type real
lemma say_fold {p:X→Y}[Fintype Y] (hv:Summable f)(V:ι→Y→ℝ): say (packing p f) V=say f (fun i=> V i ∘ p):= by unfold say; rw [tsum_fintype]; exact hauled hv (fun x=>∏ i,V i (x i))
omit [Fintype ι] in
lemma poetic (F:Field ι X)(h:Poem F)(p:X→Y): Poem (packing p F):= by
   intro w x; unfold packing cram; let h1(i:ι→X):= hinge p i;
   let t:{i// h1 i=x}≃ {i//h1 i=x ∘ w} := (Equiv.subtypeEquiv (Equiv.arrowCongr w.symm (Equiv.refl X)) (by
      intro y; change _=x ↔ h1 y ∘ w=x ∘ w; exact ⟨fun e=> by rw [show h1 y=x from e],fun e=> w.surjective.forall.mpr (show ∀ i,h1 y (w i)=x (w i) from fun i=>congr_fun e i)|>funext⟩))
   rw [← t.tsum_eq]; apply tsum_congr; intro i; apply h
end YM.Contacts.Shuttle
