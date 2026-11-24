import YM.Comparison.RG02.Moving.Launch
/-! Pure jet account for exponential (thermal pad) outside nilpotent ideal. Composes by Moving
path calculus along ℝ and then *adds* log before entropy order extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symmetry.Ribbon
open Function Filter Finset MeasureTheory RG Precision Lattice
open PertExtension.Series PertExtension.Series.Tested
open Moving Moving.Path Moving.Shift Marker Multi Order Laplace
open YM.Extra.Trajectories (connected)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {V:Type} [Fintype V] [DecidableEq V] (R : Census V) (r : ℕ)
local notation "B"=> Board R r
local notation "ν"=> fuse R r
variable (f : ℝ→ℂ)

def smooth (φ : ℝ→ℂ) := ContDiffAt ℝ ω φ 0
def heat (t:ℝ) : Grade R r:= f t • 1
omit [Fintype V] in
private lemma cash (s:R.Mode) (x:ℂ) : ((x:ℂ) • (1:Poly R)).part s= if s=R.quiet then x else 0 := by simp only [Poly.part_smul,Poly.one_part]; split <;> simp

lemma heat_seen (h : smooth f) : Seen (heat R r f):= by
    constructor; intro i; simp_rw [heat,cash]; split; exact h; exact contDiffAt_const
lemma heat_save : ∀ t, Order.Symmetric (heat R r f t) := fun _=>Order.Symmetric.one.smul _
def spring : Grade R r:= ν (heat R r f)
lemma stamped : (spring R r f).part ((B).quiet)= f 0 := by rw [spring, stamp0, heat, cash,if_pos rfl]
lemma sprouted : denominator (spring R r f)=spring R r f:= by
    unfold spring; rw [absorb]; unfold denominator; rw [show (fun t=>bottom R r (heat R r f t))=heat R r f from funext fun t=>by unfold heat; rw [map_smul,map_one]]
-- exact exponent identity on the evaluated root powers
private def low (y:ℝ) := ∑ i∈range (r+1), (i.factorial:ℝ)⁻¹ * y^i
private lemma low_smooth : ContDiff ℝ ω (low r) := ContDiff.sum (fun _ _=> contDiff_const.mul (contDiff_id.pow _))
private lemma low_lemma (i k:ℕ) : iteratedDeriv k (fun x:ℝ=> (i.factorial:ℝ)⁻¹ * x^i) 0=if i=k then 1 else 0:= by
    rw [iteratedDeriv_const_mul _ (contDiffAt_id.pow _)]
    rw [iteratedDeriv_pow]; by_cases he : i=k
    · subst i; norm_num [Nat.descFactorial_self,inv_mul_cancel₀ (show (k.factorial:ℝ)≠0 from by positivity)]
    cases lt_or_gt_of_ne he with
    | inl h => rw [Nat.descFactorial_of_lt h, Nat.cast_zero,zero_mul,mul_zero,if_neg he]
    | inr h => rw [zero_pow (by omega),mul_zero,mul_zero,if_neg he]
private lemma equals_at (k : ℕ) (h : k≤r) : iteratedDeriv k (low r) 0= iteratedDeriv k Real.exp 0 := by
    have hu : iteratedDeriv k Real.exp 0=1:= by simpa using congrFun (iteratedDeriv_exp_const_mul k 1) 0
    -- snd continuous small.
    rw [show low r = (∑ i∈range (r+1),(fun x:ℝ=> (i.factorial:ℝ)⁻¹ * x^i)) from funext fun x=>by rw [Finset.sum_apply]; rfl]; rw [iteratedDeriv_sum]; simp_rw [low_lemma]; rw [sum_ite_eq',if_pos (mem_range_succ_iff.mpr h),hu]; exact fun _ _=> (contDiffAt_const.mul (contDiffAt_id.pow _))
private lemma anchor (k : ℕ) (h : k≤r) : (iteratedFDeriv ℝ k (low r) 0)=iteratedFDeriv ℝ k Real.exp 0 := by
    ext; exact equals_at r k h
variable {g : ℝ→ℝ} (h : ContDiffAt ℝ ω g 0) (hv : g 0=0)
include h hv
private lemma board (k:ℕ) (he:k≤r) : iteratedFDeriv ℝ k (low r ∘ g) 0=iteratedFDeriv ℝ k (Real.exp ∘ g) 0 := by
    have hp:= (low_smooth r).contDiffAt (x:=g 0); have hh: ContDiffAt ℝ ω Real.exp (g 0) := by fun_prop
    rw [iteratedFDeriv_comp hp h le_top, iteratedFDeriv_comp hh h le_top,hv]; unfold FormalMultilinearSeries.taylorComp
    refine sum_congr rfl fun c hc=> ContinuousMultilinearMap.ext fun v=>?_
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
    rw [anchor r _ (c.length_le.trans he)]

private lemma guard (n k:ℕ) (he:k≤n) : motion (fun x:ℝ=> (↑(low n (g x)):ℂ)) k=motion (fun x:ℝ=> (↑(Real.exp (g x)):ℂ)) k := by
    have hl : ContDiffAt ℝ k (low n ∘ g) 0 := ((low_smooth n).contDiffAt.comp _ h).of_le le_top; have he': ContDiffAt ℝ k (Real.exp ∘ g) 0:= h.exp.of_le le_top
    change motion (Complex.ofRealCLM ∘ low n ∘ g) k=motion (Complex.ofRealCLM ∘ Real.exp ∘ g) k
    rw [motion, motion, ← Assembly.jet_apply_left Complex.ofRealCLM _ _ hl, ← Assembly.jet_apply_left Complex.ofRealCLM _ _ he']; unfold Assembly.jet; rw [board n h hv k he]

lemma expo : spring R r (fun x=> (↑(Real.exp (g x)):ℂ))= Poly.pass (spring R r (fun x=> (↑(g x):ℂ))) := by
    let k:= fun x:ℝ=> (↑(g x):ℂ); have he: Seen (heat R r k):= heat_seen _ _ _ (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 h)
    have hr: r ≤ Fintype.card (V⊕Fin r):=by simp
    let m:=Fintype.card (V⊕Fin r)
    have hh (x:ℝ): Poly.pass (heat R r k x)=heat R r (fun y=> (↑(low m (g y)):ℂ)) x := by
       unfold low heat Poly.pass; simp only [Complex.ofReal_sum,Finset.sum_smul, smul_pow,one_pow, smul_smul]; refine sum_congr rfl fun i _=>?_ ; unfold k; push_cast; rfl
    rw [spring,spring, ← (fuse_pass he).2, show (Poly.pass ∘ heat R r k)=_ from funext hh]; rw [fuse_time,fuse_time]
    apply Finset.sum_congr rfl; intro i hi; congr 1; ext s; simp_rw [sight_at,heat,cash]; split; exact (guard h hv m i ((mem_range_succ_iff.mp hi).trans hr)).symm; rfl

lemma logWallet : logVac (spring R r (fun x=> (↑(Real.exp (g x)):ℂ)))= spring R r (fun x=> (↑(g x):ℂ)) := by rw [logVac,sprouted,expo R r h hv,Cumulants.connected_pass]; rw [stamped,hv]; rfl
omit hv h
lemma scale_retain (u : ℂ) : spring R r (fun _=> u)= u • 1 := fuse_save _
lemma denominations (p q:ℝ→ℂ) (h:smooth p) (hp:smooth q) : spring R r (p+q)=spring R r p+spring R r q:= by
   unfold spring; rw [show heat R r (p+q)= _ from funext fun x=> add_smul (p x) (q x) (1 : Grade R r)]; exact fuse_add (heat_seen R r p h) (heat_seen R r q hp)
end YM.Comparison.RG02.Symmetry.Ribbon
