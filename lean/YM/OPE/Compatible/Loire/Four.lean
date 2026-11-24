import YM.OPE.Compatible.Loire.Thumb
/-!
# Cylinder IPP for the unrescaled expectation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Shrew
open Function MeasureTheory Set Topology Metric Filter Libra PertExtension Series GaussianScore
open scoped BigOperators Classical ContDiff
variable {V I:Type*}[LinearOrder I]{i j:I}{s:Finset I}
variable [NormedAddCommGroup V][NormedSpace ℝ V][FiniteDimensional ℝ V]
variable (K:I→I→ℝ)(v:I→Module.Dual ℝ V)
lemma gumP (h:First i s)(he:j∈s.erase i): First i (s.erase j):=⟨Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase he).symm,h.1⟩, fun j hJ=> h.2 j ((Finset.erase_subset ..) hJ)⟩
lemma leaping {E:Type*}[AddCommMonoid E](F:I→I→E)(s:Finset I): (∑ a∈s, ∑ b∈s.erase a,F a b)=∑ b∈s,∑ a∈s.erase b,F a b:=by
   let g(a b):=if a=b then (0:E) else F a b
   rw [show (∑ a∈s,∑ b∈s.erase a,F a b)=∑ a∈s,∑ b∈s,g a b from Finset.sum_congr rfl (fun i hi=> by rw [← Finset.sum_erase_add s (g i) hi, show g i i=0 from (if_pos rfl),add_zero]; exact Finset.sum_congr rfl (fun j hJ=>(if_neg (Finset.ne_of_mem_erase hJ).symm).symm)), Finset.sum_comm]; symm; exact Finset.sum_congr rfl (fun i hi=> by rw [← Finset.sum_erase_add s (fun a=>g a i) hi, show g i i=0 from if_pos rfl,add_zero]; exact Finset.sum_congr rfl (fun j hJ=>(if_neg (Finset.ne_of_mem_erase hJ)).symm))
def poke (x:V)(F:V→ℝ)(p:V):= fderiv ℝ F p x
lemma pokeA (x:V){p q:V→ℝ}(hp:Bond p)(hq:Bond q): poke x (p*q)=poke x p*q+p*poke x q:=by
    funext y; unfold poke; rw [fderiv_mul (hp.smooth.differentiable (by simp) y) (hq.smooth.differentiable (by simp) y)]; simp only [Pi.add_apply,Pi.mul_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul]; ring
lemma pokeB (x:V){a b:V→ℝ}(hp:Bond a)(hq:Bond b):poke x (a-b)=poke x a-poke x b:=by funext y; unfold poke; rw [fderiv_sub (hp.smooth.differentiable (by simp) y) (hq.smooth.differentiable (by simp) y)];rfl
lemma pokeC (x:V){a: V→ℝ}(hp:Bond a)(r:ℝ):poke x (r • a)=r • poke x a:=by funext y; unfold poke; rw [fderiv_const_smul (hp.smooth.differentiable (by simp) y)];rfl
omit [LinearOrder I] in
lemma pokeD (x:V)(a:I→V→ℝ)(h:∀ i∈s,Bond (a i)): poke x (∑ i∈s,a i)=∑ i∈s,poke x (a i):=by funext y; unfold poke; rw [fderiv_sum (fun i hi=> (h i hi).smooth.differentiable (by simp) y), _root_.sum_apply,Finset.sum_apply] -- names
lemma pokeP (a: Module.Dual ℝ V)(v:V):poke v a=fun _=>a v:= funext fun y=> by unfold poke; erw [(LinearMap.toContinuousLinearMap a).fderiv];rfl
lemma poHer (x:V)(s:Finset I):poke x (fauna K v s)=∑ i∈s,v i x • fauna K v (s.erase i):=by
   induction s using Finset.strongInduction with | _ s ih
   obtain rfl|hh:=s.eq_empty_or_nonempty
   · rw [fanE, Finset.sum_empty]; funext y; simp [poke]
   let a:=s.min' hh; let t:=s.erase a; have hs:t ⊂ s:= Finset.erase_ssubset (Finset.min'_mem ..); have he:=innerA hh
   let f:=fauna K v; have hp(i:I)(_h:i∈ t): Bond (K a i • f (t.erase i)):=Bond.scale _ (incense ..)
   let h(i:I):=K a i • f (t.erase i); let L:= ∑ i∈t,h i
   rw [pier K v he]; change poke x (⇑(v a)*f t-L) = ∑ i∈s, v i x • f (s.erase i)
   rw [pokeB x ((Bond.glyph _).mul (incense ..)) (rear h hp), pokeA x (Bond.glyph _) (incense ..), pokeP, show poke x L= _ from pokeD x h hp]
   rw [show poke x (f t)= _ from ih t hs, show (fun _ : V=> v a x)*f t= v a x • f t from rfl,← Finset.sum_erase_add s (fun i=>v i x • f (s.erase i)) he.1]; let T:=v a x
   change T • f t+_ - ∑ i∈t,poke x (h i) = _+T • f t
   have hv(i:I)(hi:i∈t): poke x (h i)= K a i • ∑ j∈t.erase i,v j x • f ((t.erase i).erase j):=by
       rw [show poke x (h i)= _ from pokeC _ (show Bond (fauna K v (t.erase i)) from incense ..) (K a i), ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hs)]
   have hw(i:I)(hi:i∈t): f (s.erase i)= ⇑(v a)*f (t.erase i)-∑ j∈t.erase i,K a j • f ((t.erase i).erase j):=by
       have hk:(s.erase i).erase a=t.erase i:=by unfold t;ext; simp [and_left_comm]
       unfold f; rw [pier K v (gumP he hi),hk]
   rw [Finset.sum_congr rfl hv, add_comm _ (T • f t), add_sub_assoc]; -- ←? a+b-c=a+(b-c) add_sub_assoc
   apply congr_arg (T • f t + · ) -- expression uses parser
   rw [show (∑ i∈ t,v i x • f (s.erase i))=∑ i∈t,v i x • (⇑(v a)*f (t.erase i)-∑ j∈ t.erase i,K a j • f ((t.erase i).erase j)) from Finset.sum_congr rfl (fun i hi=>congr_arg (v i x • ·) (hw i hi))]
   simp_rw [smul_sub, Finset.sum_sub_distrib,Finset.smul_sum,Finset.mul_sum]
   congr 1
   · exact Finset.sum_congr rfl fun i hi=> mul_smul_comm ..
   rw [leaping]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>by rw [show (t.erase j).erase i=(t.erase i).erase j from by ext; simp [and_left_comm],smul_comm]))
end YM.OPE.Shrew
