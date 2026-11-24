import YM.OPE.Compatible.Gum.Link
/-!
# observer syntax. separated and cross taps associated to same representative at H origins. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
variable [DecidableEq J] (t:Finset J) (p:J→E→ℝ)
local notation "W" => E → ℝ
omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in lemma fi_eq (u v:J→E→ℝ)(f:W)(h:∀ i∈t,u i=v i): Tap μ L u f t= Tap μ L v f t:=by
     induction t using Finset.strongInduction with
     | _ t ih =>
       unfold Tap; rw [Tab_rec, Tab_rec]; have hx(g:W)(s:Finset J)(hp:s⊆t): drink μ L u g s=drink μ L v g s:=congr_arg (fun a:W=> L.average μ (g*a)) (Finset.prod_congr rfl fun i hi=>h _ (hp hi)); rw [hx f _ le_rfl]; apply congr_arg; refine Finset.sum_congr rfl fun i hi=>congr_arg₂ _ (ih _ (vesselC hi) (fun j hj=>h j ((vesselC hi).le hj))) (hx _ _ (Finset.sdiff_subset ..))
def Cosis (p:J→E→ℝ)(g:W)(a:J):J→E→ℝ:=Function.update p a g
def πc (f g:W)(i:J):ℝ:= Tap μ L (Cosis p g i) f (insert i t)
lemma cpair (a:J)(f g:W)(h:a∉t):πc μ L t p f g a=Tap μ L p (f*g) t-Con (Tap μ L p f) (Tap μ L p g) t:=by
      let q:=Cosis p g a; have he := (loopIn (μ:=μ) (L:=L) t a q h f); have ha:q a=g:= update_self ..; rw [ha] at he; have hx (s)(hs:s⊆t)(v:W): Tap μ L q v s=Tap μ L p v s:=fi_eq _ _ _ _ _ _ fun u hu=>by unfold q Cosis; rw [Function.update_of_ne (show u≠a from fun e=> h (hs (e ▸ hu)))]
      apply eq_sub_of_add_eq; rw [← hx t le_rfl]; rw [he]; apply congr_arg; unfold Con; exact sum_congr rfl fun i hi=> congr_arg₂ _ (hx _ (mem_powerset.mp hi) f).symm (hx _ (sdiff_subset ..) g).symm
lemma πc_plus (q:J)(h:q∉t)(f g u:W)(hp: okP p t)(hx:Bond f)(hg:Bond g)(hu:Bond u): πc μ L t p f (g+u) q=πc μ L t p f g q + πc μ L t p f u q:=by
     rw [cpair μ L t p q _ _ h, cpair μ L t p q _ _ h, cpair μ L t p q _ _ h, mul_add, Tap_merge _ _ _ _ hp _ _ (hx.mul hg) (hx.mul hu)]; rw [show Con _ (Tap μ L p (g+u)) t=Con (Tap μ L p f) (Tap μ L p g) t+Con (Tap μ L p f) (Tap μ L p u) t from ?_]; ring
     unfold Con;rw [← Finset.sum_add_distrib];exact Finset.sum_congr rfl fun i hi=>by rw [Tap_merge _ _ _ _ (fun i hi=>hp _ ((mem_sdiff.mp hi).1)) _ _ hg hu,mul_add]
lemma πc_batches (q:J)(h:q∉t)(f:W)(g:I→W)(u:Finset I)(hp:okP p t)(hx:Bond f)(hg:∀ i∈u,Bond (g i)): πc μ L t p f (∑ i∈u,g i) q=∑ i∈u,πc μ L t p f (g i) q:=by
     induction u using Finset.induction_on with
     | empty=> rw [sum_empty,sum_empty,cpair μ L t p q _ _ h,mul_zero]; have hs(s):Tap μ L p 0 s=0:=by simpa only [zero_smul,zero_mul] using Tap_scale μ L p f 0 s
               rw [hs]; unfold Con; simp only [hs,mul_zero, sum_const_zero,sub_zero]
     | insert i u hi ih=> rw [sum_insert hi,sum_insert hi,πc_plus _ _ _ _ _ h _ _ _ hp hx (hg i (mem_insert_self ..)) (show Bond (∑ i∈u,g i) from Sumbond _ _ fun i hi=> hg _ (mem_insert_of_mem hi)), ih fun i hi=> hg _ (mem_insert_of_mem hi)]
lemma πc_along (u:J)(h:u∉t)(g:W)(hg:Bond g)(f:I→W)(s:Finset I)(hp:okP p t)(hf:∀ i∈s,Bond (f i)): πc μ L t p (∑ i∈s,f i) g u=∑ i∈s,πc μ L t p (f i) g u:=by
    unfold πc; refine prices μ L _ _ ?_ s _ hf; intro i hi; rcases Finset.mem_insert.mp hi with hh|hh; · subst i; rw [Cosis,Function.update_self]; exact hg
    rw [Cosis, Function.update_of_ne (fun (v:i=u)=> h (v ▸ hh))]; exact hp _ hh
end YM.OPE.Libra.Shell
