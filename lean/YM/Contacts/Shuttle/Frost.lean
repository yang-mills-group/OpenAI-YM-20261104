import YM.Contacts.Shuttle.Loads
/-!
# Evaluating formal rings at moments. Costs polynomials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Shuttle
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Pulse Spine
open Milling Milling.Steam Milling.Forge Milling.Garf Tensor
open scoped Classical Topology BigOperators NNReal ENNReal Matrix ContDiff
variable {G:Gauge}{X Y ι κ Z E : Type}[Fintype ι][NormedAddCommGroup E][NormedSpace ℝ E]{s t:ℝ≥0}{b c:ℝ}{h k n:ℕ}{a:X}{F:Field ι (Node X)}
-- price works at all positive exponents; support parameter α permits post-bounded charges, can also use pre-block book(s)
def hail (n:ℕ)(s:ℝ):ℝ:= n.factorial*Real.exp s/s^n
lemma hail_one (h:0<(s:ℝ))(k:ℕ)(x:ℝ)(hx:0≤x): (1+x)^k ≤ hail k s*Real.exp ((s:ℝ)*x):= by
   have hv:= (div_le_iff₀ (show 0<(k.factorial:ℝ) by positivity)).1 (Real.pow_div_factorial_le_exp ((s:ℝ)*(1+x)) (by positivity) k); rw [mul_pow, mul_add (s:ℝ),mul_one,Real.exp_add] at hv; unfold hail; field_simp; rw [mul_comm x]; linarith only [hv]
private noncomputable def rim (x:ι→Node X) := Finset.univ.sup (fun i=> Laurent.size (x i).1)
lemma rim_left (x:ι→Node X)(i:ι): size (x i).1 ≤ rim x := Finset.le_sup (f:= fun i=>Laurent.size (x i).1) (Finset.mem_univ i)
lemma rim_high (x:ι→Node X): Real.exp (s*(rim x:ℝ)) ≤ fee (terrain s X) (0,a) x:= by
   unfold rim; cases isEmpty_or_nonempty ι with
   | inl H=> simp only [Finset.univ_eq_empty,Finset.sup_empty,Nat.bot_eq_zero,Nat.cast_zero,mul_zero,Real.exp_zero]; exact fee_one _
   | inr H=>
      obtain ⟨i,-,ht⟩:= Finset.exists_mem_eq_sup (s:=univ) univ_nonempty (fun i:ι=> Laurent.size (x i).1);
      rw [ht]; have he:=fee_leg (l:=terrain s X) (o:=(0,a)) x i; convert he using 1; change _=Real.exp _; congr 3; all_goals try simp
abbrev blast (x:Node X) : ℝ:= 1+size x.1
lemma blasted (z:ι→Node X)(i:ι): blast (z i) ≤ 1+(rim z:ℝ):= add_le_add_right (Nat.cast_le.mpr (rim_left z i)) _
def Ice (v : X→ E)(w:X→ℝ)(C:ℝ):Prop :=∀ i, ‖v i‖ ≤ C*w i -- remove sec NormedAdd duplicate?
lemma fame (hc:0≤c)(hs:0<s)(z:ι→Node X): ∏ i:ι,(c*(blast (z i))^n) ≤ (c^Fintype.card ι * hail (n*Fintype.card ι) s)* fee (terrain s X) (0,a) z:= by
   let x:= (rim z:ℝ); have hx : 0≤x:=by unfold x; positivity
   refine (prod_le_prod (g:=fun i => c*(1+x)^n) (f:=fun i:ι=> c*blast (z i)^n) (fun i _=>by unfold blast; positivity) (fun i _=> mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold blast; positivity) (blasted z i) _) hc)).trans ?_; rw [prod_const,mul_pow,← pow_mul,mul_assoc]; change c^Fintype.card ι*_ ≤ c^Fintype.card ι* _; exact mul_le_mul_of_nonneg_left ((hail_one hs _ x hx).trans (mul_le_mul_of_nonneg_left (rim_high z) (by unfold hail; positivity))) (pow_nonneg hc _)
lemma Rest.rims (H:Rest (terrain s X) (0,a) F b)(hs:0<s)(hc:0≤ c)(n:ℕ): SumBudget (fun z=> ‖F z‖* (∏ i:ι,c*blast (z i)^n)) (b * (c^Fintype.card ι * hail (n*Fintype.card ι) s)):= by
   let d:=c^Fintype.card ι* hail (n*Fintype.card ι) s; have ht:0≤d:= by unfold d hail; positivity
   rw [mul_comm b]; refine budget_mono (budget_scale ht H) (fun _=>mul_nonneg (norm_nonneg _) (prod_nonneg (fun i _=> mul_nonneg hc (by unfold blast; positivity)))) ?_; intro z; exact (mul_le_mul_of_nonneg_left (fame hc hs z) (norm_nonneg _)).trans_eq (mul_left_comm ..)
lemma Rest.calls {v:ι→Node X→ℝ}(H:Rest (terrain s X) (0,a) F b)(hs:0<s)(hc:0≤c)(hv:∀ i, Ice (v i) (fun x=> blast x^n) c) : Summable (fun y=> F y*∏ i:ι,v i (y i)) := by
    refine Summable.of_norm ((H.rims hs hc n).2.1.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=>?_ ); rw [norm_mul,norm_prod]; exact mul_le_mul_of_nonneg_left (prod_le_prod (fun i _=> norm_nonneg _) (fun j _=> hv j _)) (norm_nonneg _)
section arrival
variable {v:ι→Node X→ℝ}{w:ℕ→ι→Node X→ℝ}
theorem settling (H:Rest (terrain s X) (0,a) F b)(hs:0<s)(hc:0≤c)(hw:∀ᶠ z in atTop,∀ i, Ice (w z i) (fun x=> blast x^n) c)(hv:∀ i j,Tendsto (fun z=> w z i j) atTop (𝓝 (v i j))) : Tendsto (fun z=>say F (w z)) atTop (𝓝 (say F v)):= by
    refine tendsto_tsum_of_dominated_convergence (α:=ℕ) (H.rims hs hc n).2.1 (fun i=> Tendsto.const_mul _ (tendsto_finsetProd _ (fun _ _=> hv _ _))) (hw.mono (fun i hi j=>?_)); rw [norm_mul,norm_prod]; exact mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=> norm_nonneg _) (fun k _=>hi k _)) (norm_nonneg _)
end arrival
-- linear reads on ambient platforms of fixed norm
variable (k)
def blanket {X : Type} (f:Field (Fin k) X)(P: X→ E →L[ℝ] ℝ)(z:Fin k→X) : T E ℝ k := (ContinuousMultilinearMap.mkPiRing ℝ (Fin k) (f z)).compContinuousLinearMap (fun i=> P (z i))
def sheet (f:Field (Fin k) (Node X))(P: Node X → E→L[ℝ] ℝ) : T E ℝ k:=∑' z, blanket k f P z
variable {k} {f : Field (Fin k) (Node X)}{P: Node X → E→L[ℝ] ℝ}
lemma blanket_spend (H:Rest (terrain s X) (0,a) f b)(hs:0<s)(hc:0≤c)(hv:Ice P (fun x=> blast x^n) c):
    SumBudget (fun z=> ‖blanket k f P z‖) (b*(c^k* hail (n*k) s)):= by
   have hr := H.rims hs hc n; rw [Fintype.card_fin] at hr; refine budget_mono hr (fun _=> norm_nonneg _) (fun i=>?_); unfold blanket; apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); rw [ContinuousMultilinearMap.norm_mkPiRing]; exact mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=> norm_nonneg _) (fun _ _=> hv _)) (norm_nonneg _)
@[simp] lemma blanket_response {X : Type} (f:Field (Fin k) X)(A: X→ E →L[ℝ] ℝ)(z:Fin k→X)(u:Fin k→E) : blanket k f A z u=f z*∏ i:Fin k, A (z i) (u i):= by unfold blanket; rw [mul_comm]; rfl
lemma sheet_read (h: Summable (blanket k f P))(u:Fin k→E) : sheet k f P u=say f (fun i x=>P x (u i)):= by
    have ht:= (ContinuousMultilinearMap.apply ℝ (fun _=> E) ℝ u).hasSum h.hasSum; unfold say; simp_rw [← blanket_response]; exact ht.tsum_eq.symm
end YM.Contacts.Shuttle
