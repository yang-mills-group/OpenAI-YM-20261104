import YM.Contacts.Loom.Ream
/-! Arbitrary point/seam evaluation markets. Clock after.Stage.Star. Uniformly weighted relative spaces.
 A Motion r charges scale‐normalized `cap` using actual n.Point Metrics. -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Meter
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
variable {E F V Y α γ:ℕ→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (F i)] [∀ i,NormedSpace ℝ (F i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (Y i)][∀ i,NormedSpace ℝ (Y i)]
variable {N:Meter}{p q r s Z:ℝ}{k j l:ℕ}{f:ℕ→ℝ}
namespace Patch
open Capture PertExtension.Series Radial Milling Tensor
variable {d D g a:ℕ→ℝ} {n:ℕ} [∀ i,FiniteDimensional ℝ (E i)] [∀ i,FiniteDimensional ℝ (F i)] [∀ i,MeasurableSpace (V i)][∀ i,BorelSpace (V i)] [∀ i,MeasurableSpace (F i)] [∀ i,BorelSpace (F i)]
variable {U W:Trunk E V}{μ: ∀ i,Measure (V i)} [∀ i,IsProbabilityMeasure (μ i)]
variable {R:ℕ→ Trunk E V} {b:Shelf E V F}{f:Lamp F}
lemma Board.exactness (hU:Board d U)(hh: W=U): Board d W:= by rw [hh]; exact hU
lemma Board.mul (h:Board d U)(hp:Board d W):Board d (U*W):= (h.and hp).mono fun i hi x hx=>(hi.1 x hx).mul (hi.2 x hx)
lemma Board.weighted (h: Board d U)(a:ℝ) : Board d (a • U):= h.mono fun i hi x hx=> (hi _ hx).const_smul a
lemma Board.const (K:ℝ): Board (E:=E) (V:=V) d (fun _ _ _=>K):= Eventually.of_forall fun _ _ _=> measurable_const
lemma Board.stair' (h:∀ i≤n,Board d (R i))(v k:ℕ)(hp:k≤n): Board d (stair R v k):= by
   induction v generalizing k with
   | zero=> unfold stair; split; exact Board.const 1; exact Board.const 0
   |succ i ih=>
     refine Board.fin (HasAntidiagonal.antidiagonal k) _ (fun v hv=>?_) -- not name conflict
     have hh:= HasAntidiagonal.mem_antidiagonal.mp hv; exact Board.mul (ih _ (by omega)) (h _ (by omega))
lemma Board.roster (h:∀ i≤n,Board d (R i))(v k:ℕ)(hp:k≤n): Board d (rol R v k):= by unfold Capture.rol; rw [Finset.sum_apply]; exact Board.fin _ _ fun i _=> (Board.stair' h _ _ hp).weighted _
-- θ timeline.
variable (hS: Shell N μ D)(he:Root N f k 0 a)(hD:Pouch N stashp a)(hg:Pouch N (-(1/2)) g)(hf:Narrow N k fit d D b)(hu:Joint N k fit d b)
    (hm:∀ᶠ i in atTop, Measurable (f i) ∧ ∀ x∈Frame.Bank E d i,Measurable (fun z:V i=> b i z x))(ht:n+3≤k)
local notation "L" => (codes f g b)
local notation "R₀" => rol (codes f g b) n
local notation "P" => Frame.Port E d
local notation "K" => (Capture.expn (Capture.pulse f g b))
include he hD hg hu ht
lemma smoke (hx:j≤n) : Joint N k 0 d ((R₀) j):= by
   let A:= codes f g b; have hp i (hp:i≤j): Joint N k 0 d (A i):= by
      by_cases hr:i=0; · subst i; unfold A; rw [codes_omit]; exact Joint.zero
      have h:= he.worth hD (show i+2≤ k from by omega); have hb:N.Rush 1 (fun i=>-((g i)⁻¹^2)):= by have h:= (Loom.Rush.absSq hg.back).multiplier (-1); norm_num at h; simpa only [inv_pow] using h
      refine Joint.ascend (Joint.weighted (Joint.sheet hu h) hb rfl) ?_ le_rfl ?_; · unfold fit; push_cast; have hz: (1:ℝ)≤(i:ℝ):=(by exact_mod_cast (show 1≤ i from Nat.one_le_iff_ne_zero.mpr hr)); linarith only [hz]
      exact hg.pos.mono fun i' hi=> funext₂ fun k x=> sees_radius i hr _ _ x hi.ne'
   exact (by simpa only [zero_mul] using Joint.rollerJob hp le_rfl n j le_rfl)
include hf hm hS
lemma seam (hx:race<p)(hy:p<0): let v:= stay μ D (K); Word N (P) k n p (leaf v) (fun i=> leaf (weight μ ((R₀) i))) := by
   intro v; let s i:=weight μ (R₀ i); have hb: Board d K:= hm.mono (fun i hi x hx=> by
       let Q(z:V i):= b i z x
       let Y(z:F i):= skel (f i) 3 z; have hQ : Measurable Y:= (continuous_iff_continuousAt.mpr (fun x=>(skel_analytic (f i) 3 x).continuousAt)).measurable; exact (((hi.1.sub hQ)|>.comp (hi.2 x hx)).const_mul _).exp)
   have hk l (hl:l≤n): Board d ((R₀) l):= Board.roster (n:=n) (fun i hi=> hm.mono (fun k hk x hx=> by
      let V:= Radial.layers (f k) i; have he:Measurable V:= by unfold V Radial.layers; exact (continuous_iff_continuousAt.mpr fun x=>(jet_s (f k) (i+2) x).continuousAt).measurable.neg.add (by split; exact (continuous_iff_continuousAt.mpr fun x=>(jet_s (f k) 2 x).continuousAt).measurable; exact measurable_const)
      exact (he.comp (measurable_const.smul (hk.2 x hx))).const_mul _)) _ _ hl
   refine collects hS ?_ hb hk (fun i hi=> ⟨_,smoke he hD hg hu ht hi⟩)
   let A:= pulse f g b; let F':= wish (d:=d) (a:=D) b; let Z:= stepIn E V d D
   convert (rotor he hD hg hf ht hx hy) using 1;
   · rfl
   funext i j k x; erw [show wish ((rol (codes f g b) n) i) j k x=((rol (codes f g b) n) i) j (leg k) x from rfl, costSum, costSum]
omit he hD hg hf hm hS hu ht
lemma roll_zero (T:ℕ→Mint E α)(n:ℕ)(h:T 0=0): rol T n 0=1:= by
    let d:=Finset.range (n+1); unfold Capture.rol; rw [Finset.sum_apply,sum_eq_single_of_mem 0 (mem_range.mpr (by omega))]; · simp [stair]
    intro i _ ht; cases i; exact (ht rfl).elim; simp only [stair,Pi.smul_apply, branch]; simp [h]
lemma weight_c : weight μ (1:Trunk E V)=1:= funext₂ fun i v=>by simp [weight,probReal_univ]
include he hD hg hf hm hS hu ht
-- makes possible dividing under exponent comparisons, constants cancel
lemma neat (hx:race<p)(hy:p<0): Budget N (P) k p (leaf (stay μ D (K)) - 1) := by
   have hE:= seam hS he hD hg hf hu hm ht hx hy -- edit
   let f':= fun i=> leaf (d:=d) (weight μ ((R₀) i)); let A (i:ℕ):= Capture.stair f' 0 i; have hp: Word N (P) k n p 1 A:= by simpa only [pow_zero] using (hE.powers 0)
   refine (hE.sum hp.opp).plush ?_; simp only [Pi.add_apply,Pi.neg_apply,roll_zero (codes f g b) n (codes_omit f g b),weight_c]; change ((leaf (1:Lamp E)) + -( (1:Mint E _)))=_; exact add_neg_cancel _
end Patch
end
end YM.Contacts.Loom
