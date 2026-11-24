import YM.AveragedStep.Moments.Tall
/-!
# Currency for local gates and normalized products

An exponential index weight of any positive rate (to be required sufficiently
small against deterministic propagation); β^δ losses admissible, logarithmic
cost here sharper. EL law covers arbitrary correlated products, even when
addresses/markers are repeated. Gates of finite radius around *held* links
cost every coupling power here (χ fixed trigger in group units, not divided
by τ or a shrinking threshold!). WP1 is an integrated probability estimate,
after the noise divisor already. NOT a `Valid` E,K estimate: there is no
license here to spend the current receipt with a forced/divisor hit, or
against the unconditioned coarse Haar. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG Loops Tree MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}

abbrev Rim (c f:Side):=Edge (Site f) ⊕ Edge (Site c)
def atRim (S:StepData c f):(Rim c f) → Site f:=Sum.elim Prod.fst (S.ratio.embed ∘ Prod.fst)
def roll {S:StepData c f}(F:Forest S.ratio) (x:Site c) (z:Board G c f): (Rim c f)→ G.El:= Sum.elim (stamped S F x z.1 z.2) (setGauge x z.2)
@[fun_prop] lemma roll_cont {S:StepData c f}(F:Forest S.ratio) (x:Site c):
    Continuous (roll (G:=G) F x):=by
  apply continuous_pi; rintro (a|a)
  · exact (continuous_apply a).comp (stamp_cont S F x)
  exact (continuous_apply a).comp ((gauge_cont x).comp continuous_snd)

def spokes {S:StepData c f}(F:Forest S.ratio)(τ:ℝ)(x:Site c)(e:Rim c f):Query S G:= fun _ z=> τ*G.chord (roll F x z e)
variable {S:StepData c f}(F:Forest S.ratio)
lemma spoke_admits (x e τ): Admits (spokes (G:=G) F τ x e):=fun _ => env_continuous (by unfold spokes; fun_prop)
lemma spoke_pos {τ:ℝ}(ht:0≤τ)(x e)(i:S.Choices)(y:Board G c f): 0 ≤ spokes F τ x e i y := mul_nonneg ht (G.chord_nonneg _)

/-- geometric condition only on sides/regulator, not on number or position
of marks. -/
structure Window {c f:Side}(G:Gauge)(S:StepData c f)(τ:ℝ) (P:Patch) (K:KernelChoices) : Prop where
 shape : S.patch=P
 control : S.kernel=K
 fourth : 4∣f.val
 reach : (Real.log τ)^2≤ (c.val:ℝ)
 margin : 20*P.L.val+20<f.val

omit F in
lemma spoke_price (G:Gauge) (P:Patch)(K:KernelChoices)(h:P.Branches K G)(k:ℕ)(a:ℝ)(ha:0<a):
    ∃ C:ℝ,0≤C∧∀ᶠ τ:ℝ in atTop,∀{c f:Side}(S:StepData c f)(F:Forest S.ratio), Window G S τ P K →
    ∀ (x:Site c)(e:Rim c f), Ranked τ (spokes (G:=G) F τ x e) k
       (C*lag τ ^k * plume a (S.ratio.embed x) (atRim S e)):=by
 obtain ⟨C,hC,H⟩:=fine_breeze G P K h a ha k
 obtain ⟨D,hD,T⟩:=tall_price G P K h a ha k
 refine ⟨max C D,le_trans hC (le_max_left ..),?_⟩
 filter_upwards [eventually_ge_atTop (1:ℝ),H,T] with τ ht he hw c f S F w x e
 have hv:=lag_ge ht
 rcases e with i|i
 · exact (hw S F w.shape w.control w.fourth w.reach w.margin x i).enlarge <| mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity)) (plume_pos ..).le
 exact (he S w.shape w.control w.fourth w.reach x i).enlarge <| mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)) (plume_pos ..).le

-- allow any queries dominated by those costs (e.g. global chord/chart/curvature components)
def hops {I:Type*}[Fintype I](x:Site f)(y:I→Site f) : ℝ := ∑ i,separation x (y i)
lemma hops_pos {I:Type*}[Fintype I](x:Site f)(y:I→Site f): 0≤hops x y:=by unfold hops; positivity
lemma plume_hops {I:Type*}[Fintype I](x:Site f)(y:I→Site f)(j:I){a:ℝ}(ha:0≤a):plume a x (y j) ≤ Real.exp (a*hops x y):=by
 unfold plume; gcongr; exact Finset.single_le_sum (f:=fun i=>(separation x (y i):ℝ)) (fun i _=> Nat.cast_nonneg _) (Finset.mem_univ _)

omit F in
lemma spoke_product (G:Gauge)(P:Patch)(K:KernelChoices)(h:P.Branches K G)(k:ℕ)(a:ℝ)(ha:0<a)(M:ℝ)(hM:0≤M):
    ∃ C:ℝ,0≤C∧∀ᶠ τ:ℝ in atTop,∀{c f:Side}(S:StepData c f)(F:Forest S.ratio), Window G S τ P K→
    ∀ (x:Site c)(e:Fin k→Rim c f)(q:Fin k→Query S G),
       (∀ j, Admits (q j)) →
       (∀ j i z,S.likelihood z.1 i≠0 → |q j i z| ≤ M*spokes F τ x (e j) i z)→
       readQ S (τ^2) (fun i z=>∏ j,|q j i z|) ≤
       C * lag τ ^ k * Real.exp (a*hops (S.ratio.embed x) (atRim S ∘ e)):=by
 obtain ⟨C,hC,H⟩:= spoke_price G P K h k a ha
 refine ⟨1+k*(M^k*C),by positivity,?_⟩
 filter_upwards [H,eventually_ge_atTop (1:ℝ)] with τ H ht c f S F hw x e q hs hy
 let b:=S.ratio.embed x
 let W:=Real.exp (a*hops b (atRim S ∘ e))
 have hb:S.patch.Branches S.kernel G:=by rw [hw.shape,hw.control]; exact h
 let L:=lag τ^k
 have he:1≤L:=one_le_pow₀ (lag_ge ht)
 have h0L:=zero_le_one.trans he
 have hW:1≤W:= Real.one_le_exp (mul_nonneg ha.le (hops_pos ..))
 have hf (j:Fin k): Ranked τ (q j) k (M^k*(C*L*W)):=by
    have hd:=H S F hw x (e j)
    have hz:=hd.enlarge (mul_le_mul_of_nonneg_left (plume_hops b (atRim S ∘ e) j ha.le)
        (by positivity : 0 ≤ C*L))
    rw [← abs_of_nonneg hM]
    apply Ranked.below hb (q:=M • spokes F τ x (e j)) (hs j) (hz.scale M)
    intro i z hi; rw [show (M • spokes F τ x (e j) : Query S G) i z=M*spokes F τ x (e j) i z from rfl]
    exact (hy j i z hi).trans (le_abs_self _)
 apply (Ranked.many hb Finset.univ _ _ fun j _=> (show Ranked τ (q j) Finset.univ.card (M^k*(C*L*W)) by simpa using hf j)).trans
 rw [Finset.sum_const, Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
 nlinarith only [one_le_mul_of_one_le_of_one_le he hW] -- L/W aliases
end YM.AveragedStep
