import YM.AveragedStep.Recursion.Pound
/-!
# Trial criteria for conditional lattice coefficient program
It is useful to separate the lattice SD equation (algebraic, to be built
independently) from the physical correlation accounting. Keep smoothing
conventions and physical growth (which rely on pins) separate.
Here the physical residual relationship is proved for any such *formal* input;
must still BUILD this then price all-orders outputs, don't use as final input. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep.SD
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Finsupp
variable {c f:Side}{G:Gauge}{S:StepData c f}

structure Azure (A:ChartRatio G)(F:Forest S.ratio) where
  trial:ℕ→Hand G c f→ Lips G c f→ℝ
  fair {w u}(he:List.Perm w u)(Y n) : trial n Y w=trial n Y u
  fixed {w e}(he:e∈F.trunks)(i:G.ColorIndex)(h:(Sum.inl e,i)∈w)(Y n) : trial n Y w=0
  cutoff {w}(h:clips w=0)(Y n):trial n Y w= if n=0 then sample Y w else 0
  price (n:ℕ)(w):Continuous (fun v:Hand G c f=> trial n v w)
  wall {X Y:Hand G c f} (h:∀ z:Edge (Site c),X (Sum.inr z)=Y (Sum.inr z))(w:Lips G c f)(n:ℕ):trial n X w=trial n Y w
  score (w:Lips G c f)(j:Key F G)(n:ℕ)(Y:Hand G c f):
     offer (trial n Y) (weigh F A j w)=offer (trial n Y) (friends F A j w)-∑ i∈active n, offer (trial (n-i) Y) (leap (A:=A) S (fkey F j) i w)

variable {F:Forest S.ratio}{A:ChartRatio G}
def Azure.span (U:Azure A F)(k:ℕ)(t:ℝ)(Y:Hand G c f):Lips G c f→ℝ:=∑ n∈Finset.range (k+1),t^n • U.trial n Y
lemma Azure.span_smooth (U:Azure A F)(t:ℝ)(w:Lips G c f)(d:ℕ): Continuous (fun Y:Hand G c f=> U.span d t Y w):=by
 unfold Azure.span; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact continuous_finsetSum _ (fun i _=> continuous_const.mul (U.price ..))
lemma Azure.span_perm (U:Azure A F)(t:ℝ){v w}(hp:List.Perm v w)(d:ℕ)(Y):U.span d t Y v=U.span d t Y w:=by
 simp_rw [Azure.span,Finset.sum_apply,Pi.smul_apply,U.fair hp]
lemma Azure.span_score (U:Azure A F)(k:ℕ)(t:ℝ)(Y:Hand G c f)(i:Key F G)(w):
   offer (U.span k t Y) (weigh F A i w)= offer (U.span k t Y) (friends F A i w)- ∑ j∈active k,t^j*offer (U.span (k-j) t Y) (leap (A:=A) S (fkey F i) j w):=by
 simp only [Azure.span,offer_sum,offer_smul,smul_eq_mul,U.score,mul_sub,Finset.sum_sub_distrib]
 exact congrArg (fun a:ℝ=> (∑ k'∈Finset.range (k+1),t^k' * offer (U.trial k' Y) (friends F A i w))-a) (active_power k t (fun l m=>offer (U.trial m Y) (leap (A:=A) S (fkey F i) l w)))

variable (F)(Q:Cuff S.patch S.kernel A) (x:Site c)(τ:ℝ)(f':Config G c→ ℝ)

def dirt (d:ℕ)(z:TopologyQ F G)(U:Azure A F):Lips G c f→ℝ:=sample (hands F Q x τ z)-U.span d τ⁻¹ (hands F Q x τ z)
def lessons (U:Azure A F)(d:ℕ)(w:Lips G c f):ℝ := report F (τ^2) x (fun z=>f' z.2*dirt F Q x τ d z U w)
lemma dirt_env (U:Azure A F)(d:ℕ)(w:Lips G c f):Envelope (fun z=>dirt F Q x τ d z U w):=by
 exact hands_env F Q x _ _ ((mon_cont w).continuous.sub (U.span_smooth ..))
lemma lessons_apply (H:S.patch.Branches S.kernel G)(hf:Envelope f')(U:Azure A F)(d:ℕ)(p:Spray (Lips G c f)): offer (lessons F Q x τ f' U d) p = report F (τ^2) x (fun z=>f' z.2*offer (dirt F Q x τ d z U) p):=by
 rw [show (fun z:TopologyQ F G=>f' z.2*offer (dirt F Q x τ d z U) p) =fun z=> offer (fun i=> f' z.2*dirt F Q x τ d z U i) p from ?_,offer_report F H _ x (I:=Lips G c f) (fun i z=>f' z.2*dirt F Q x τ d z U i) (fun i=> (env_comp hf measurable_snd).mul (dirt_env F Q x τ U d i)) p]
 · rfl
 funext z; refine Eq.symm (offer_smul (f' z.2) _ _)
lemma dirt_offer_env (U:Azure A F)(d:ℕ)(p:Spray (Lips G c f)):Envelope (fun z=> offer (dirt F Q x τ d z U) p):=Envelope.sum p.support (fun i=>fun z=>p i • dirt F Q x τ d z U i) (fun i=> (Envelope.const _).mul (dirt_env F Q x τ U d i)) -- order?

def rust (i:Key F G)(w:Lips G c f)(d:ℕ):ℝ:= report F (τ^2) x (fun z=> f' z.2 * vice (A:=A) (S:=S) τ⁻¹ (fkey F i) w d (hands F Q x τ z))
lemma reconcile (U:Azure A F)(t:ℝ)(i:Key F G)(Y:Hand G c f)(H:S.patch.Branches S.kernel G)(hY:pin F Y)(w)(d):
    let T(n):= sample Y-U.span n t Y
    offer (T d) (weigh F A i w)=offer (T d) (friends F A i w)- ∑ n∈active d,t^n* offer (T (d-n)) (leap (A:=A) S (fkey F i) n w)-vice (A:=A) (S:=S) t (fkey F i) w d Y:=by
 intro T; rw [← unite H F A i Y hY w t d]; simp_rw [T,bunched,offer_sub,U.span_score,map_sub,map_sum,map_smul,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]
 ring

lemma report_minus (H:S.patch.Branches S.kernel G){u v:TopologyQ F G→ℝ}(hU: Envelope u)(hV:Envelope v):report F τ x (u-v)=report F τ x u-report F τ x v:=by
 rw [sub_eq_add_neg u,report_add F x H (v:=-v) hU hV.neg,← neg_one_smul ℝ v,report_scale]; ring
lemma lessons_shift (H:S.patch.Branches S.kernel G)(hf:Envelope f')(U:Azure A F)(i:Key F G)(w)(d:ℕ) :
    let V:=lessons F Q x τ f' U
    offer (V d) (weigh F A i w)=offer (V d) (friends F A i w)- ∑ n∈active d,τ⁻¹^n*offer (V (d-n)) (leap (A:=A) S (fkey F i) n w)-rust F Q x τ f' i w d:=by
 intro V; unfold V; simp_rw [lessons_apply F Q x τ f' H hf]; unfold rust
 let q(n:ℕ)(p:Spray (Lips G c f))(z:TopologyQ F G):= f' z.2* offer (dirt F Q x τ n z U) p
 let W(n:ℕ):=q (d-n) (leap (A:=A) S (fkey F i) n w)
 let V':= fun z:TopologyQ F G=> f' z.2* vice (A:=A) (S:=S) τ⁻¹ (fkey F i) w d (hands F Q x τ z)
 have ht:Envelope (fun z:TopologyQ F G=>f' z.2):=env_comp hf measurable_snd
 have he(n p):Envelope (q n p) := ht.mul (dirt_offer_env F Q x τ ..)
 have hW(n):Envelope (τ⁻¹^n • W n):=(Envelope.const _).mul (he ..)
 let R: (TopologyQ F G→ℝ)→ℝ:=report F (τ^2) x
 change R (q d (weigh F A i w))= R (q d (friends F A i w)) - ∑ n∈active d,τ⁻¹^n*R (W n)- R V'
 have hR(n:ℕ):τ⁻¹^n * R (W n)= R (τ⁻¹^n • W n):=Eq.symm (report_scale F ..)
 simp_rw [hR]; unfold R; rw [← report_sum F x H (active d) (fun n=>τ⁻¹^n • W n) (fun i _=>hW i),← report_minus F x (τ^2) H (he d (friends F A i w)) (Envelope.sum (active d) (fun n z=> (τ⁻¹^n • W n) z) hW)]
 let B:TopologyQ F G→ℝ:=fun z=>∑ n∈active d,(τ⁻¹^n • W n) z
 let D:= q d (friends F A i w)
 have hD_B: Envelope (D-B):=by rw [sub_eq_add_neg]; exact (he ..).add (Envelope.sum (active d) _ hW).neg
 rw [← report_minus F x (τ^2) H hD_B (show Envelope V' from ht.mul (vice_env F Q w x (fkey F i) d τ))]
 congr 1; funext z
 have hz:= reconcile F U τ⁻¹ i _ H (chamber_pin F A Q x τ z) w d
 unfold D B W V' q dirt; simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
 dsimp only at hz; rw [hz]; simp only [mul_sub,Finset.mul_sum]; ring_nf
end YM.AveragedStep.SD
