import YM.Contacts.Loom.Verse
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
open Capture
variable {d D g a:ℕ→ℝ} {n:ℕ} [∀ i,FiniteDimensional ℝ (E i)] 
variable {U W:Trunk E V}{f f': Lamp E}{R T:ℕ→ Lamp E}
local notation "xX" => Frame.Port E d
abbrev meteor (f:Lamp E) : Lamp E:= fun i _=>f i 0
lemma freeze (h: Direct N k p d f)(he:∀ᶠ i in atTop, 0< d i): Direct N k p d (meteor f):= by
    refine Loom.Budget.value _ (Rush.reV (Y:=fun i=> ‖f i 0‖) ((Arms.pick_const h).lift le_rfl (he.mono fun i hi b _ h=> ?_))); rw [norm_norm]; exact h ⟨_, mem_ball_self (x:=(0:E i)) hi⟩
lemma frozen (h: Word N (xX) k n p (leaf f) (fun i=> leaf (T i)))(he:∀ᶠ i in atTop, 0<d i): Word N (xX) k n p (leaf (meteor f)) (fun i=>leaf (meteor (T i))) := by
   have hg : Direct N k (p*(n+1)) d (f-green T n):= by refine Arms.cheaper ?_ h.grade; funext i j x; simp only [Pi.sub_apply,green,leaf,Finset.sum_apply]
   refine ⟨h.quiet,fun i hi=>freeze (h.entries i hi) he, Arms.cheaper ?_ (freeze hg he)⟩; funext i j x; simp only [meteor,leaf,green,Pi.sub_apply,Finset.sum_apply]
variable {ε ε':ℝ}
abbrev logS (f:Lamp E):=fun i=> Real.log ∘ f i
abbrev expS (f:Lamp E):=fun i=> Real.exp ∘ f i
lemma bargain (h: Word N (xX) k n p (leaf f) (fun i=> leaf (R i))) (hh:Word N (xX) k n p (Capture.expn (leaf f')) (fun i=> leaf (T i))) (hk:Direct N k ε' d (f-1)) (he:∀ᶠ i in atTop, 0<d i) (hv:ε'<0)(h₁:p*(n+1)<s) (hq:s<0)(hz:1≤k) (hB:∀ᶠ i in atTop,∀ j≤n, R j i=branch (fun i=>meteor (R i)) T j i): Direct N k s d (logS f -logS (meteor f) - f'):= by
   let F:= meteor f; let u:=expS f'; let Y:=Capture.expn (leaf (d:=d) f'); have he': Word N (xX) k n p (leaf (F*u)) _:= (frozen h he).mul hh
   have hU : Budget N (xX) k (p*(n+1)) (leaf (F*u-f)):= by
        have ht:= (Capture.concordance (P:=fun i=> leaf (R i)) he' h (hB.mono fun i hi j hj=>?ht)); exact ht; case ht=> ext l y; change _= R j i y; rw [hi _ hj]; unfold branch leaf; simp only [Finset.sum_apply,Pi.mul_apply,meteor]
   have hf := Capture.positive hv (show Budget N (xX) k ε' (leaf f-1) from hk)
   refine Arms.reveal (Arms.opp (corresponding (U:=leaf f) (W:=leaf (F*u)) (x:=xX) hk hv hU hz h₁ hq)) ?_ le_rfl le_rfl; filter_upwards [hf,he] with i hv hi j; refine Eventually.of_forall fun x=>?_ ; have ht:0<F i x:= (hv ⟨_,mem_ball_self (x:=(0:E i)) hi⟩).self_of_nhds; change Real.log (f i x)-Real.log (F i x) -f' i x = -(Real.log (F i x*Real.exp (f' i x))-Real.log (f i x)); rw [Real.log_mul ht.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
-- deliver when using any u/v exposing coherence
variable [∀ i,FiniteDimensional ℝ (F i)][∀ i,FiniteDimensional ℝ (Y i)][∀ i,MeasurableSpace (V i)][∀ i,BorelSpace (V i)] [∀ i,MeasurableSpace (F i)][∀ i,BorelSpace (F i)]
   {μ: ∀ i,Measure (V i)} [∀ i,IsProbabilityMeasure (μ i)]
variable {K:Lamp F}{w:Shelf E V F}{ℓ:Lamp Y}{v:∀ i,E i→Y i}
   (hS:Shell N μ D)(hc:Root N K k 0 a)(hb:Pouch N stashp a)(hu:Pouch N (-(1/2)) g)
   (hT: Narrow N k fit d D w)(hm:∀ᶠ i in atTop, Measurable (K i)∧∀ x∈Frame.Bank E d i,Measurable (fun z:V i=> w i z x))(hf: Joint N k fit d w)(hK:n+3≤k)
def head (ℓ:Lamp Y) (g:ℕ→ℝ)(v:∀ i,E i→ Y i): Lamp E:= fun i x=> -((g i)⁻¹^2)*(ℓ i-skel (ℓ i) 3) (v i x)
abbrev irisTail (ℓ:Lamp Y) (g:ℕ→ℝ)(v:∀ i,E i→ Y i)(n:ℕ): Lamp E:= fun i x=> (g i)^n * PertExtension.Series.Radial.expsum (PertExtension.Series.Radial.layers (ℓ i)) n n ((g i)⁻¹ • v i x)
-- immediate family via powerbound.report. Need match.S
include hS hc hb hu hT hm hf hK
lemma steer (hx : race<p)(hy:p<0)(hp:p*(n+1)<q)(hq:q<0)(ht:∀ᶠ i in atTop,0<d i)(hr:Root N ℓ k 0 a)(hv:Direct N k fit d v)
    (hm' : ∀ᶠ i in atTop, let f:= weight μ ∘ rol (codes K g w) n; ∀ j≤n,f j i= branch (fun j=> meteor (f j)) (irisTail ℓ g v) j i): let U:=stay μ D (Capture.expn (Capture.pulse K g w)); Direct N k q d (logS U-logS (meteor U)-Loom.Patch.head ℓ g v):= by
     intro U; let f:= weight μ ∘ rol (codes K g w) n; apply bargain (seam hS hc hb hu hT hf hm hK hx hy) (T:=irisTail ℓ g v) ?_ (neat hS hc hb hu hT hf hm hK hx hy) ht hy hp hq (by omega) hm';
     let S := irisTail ℓ g v; let V:= rol (codes ℓ g (leaf (d:=d) v)) n; have he: ∀ i≤n,V i=leaf (S i):= by intro i hi; unfold V; rw [costSum]; funext k j x; exact congr_arg _ (congr_fun (PertExtension.Series.Radial.expsum_limit (a:=PertExtension.Series.Radial.layers (ℓ k)) (funext fun _=> PertExtension.Series.Radial.Stationary.layers_zero _) hi).symm _)
     have hg:= rotor hr hb hu hv hK hx hy; refine ⟨hy,fun i hi=> Arms.cheaper (he i hi) (hg.entries i hi),?_⟩; refine Arms.cheaper ?_ hg.grade; apply congr_arg₂ (·-·) rfl; unfold green; exact Finset.sum_congr rfl (fun i hi=>he i (Nat.le_of_lt_succ (mem_range.mp hi)))
end Patch
end
end YM.Contacts.Loom
