import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import YM.OPE.Compatible.Grafts.Beam
import YM.OPE.Compatible.Grafts.Tug
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Essay
open Gael Stranded
open Polynomial Char
-- Value tests finite-dimensional unwind. No global analytic dependence needed
private lemma polGlass (p:Polynomial ℝ):Gael (fun t:ℝ=> p.eval t):=by
     have hv:ContDiffAt ℝ ∞ (fun t:ℝ=> p.eval t) 0:=(by simpa using (Polynomial.contDiff_aeval (𝕜:=ℝ) p ∞).contDiffAt (x:=0)); refine Exists.intro _ (((Pawn.calm hv).stale (1:ℝ)).cong (Filter.Eventually.of_forall fun i=>by simp))
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]
omit [MeasurableSpace E][BorelSpace E] in
lemma pears (K: E→L[ℝ] F)(p:ℕ→E→ℝ)(h:∀ i,Bond (p i))(k:ℕ)(hp:∀ i,∃ c:ℝ, 0≤ c ∧∀ x:E, ‖p i x‖ ≤ c*(1+‖K x‖)^k)(ht:∀ x:E,Tendsto (fun i:ℕ=>p i x) atTop (𝓝 0))(x:ℝ→E)(hx:Gael x)(j:Phase): Tendsto (fun i:ℕ=>(trill (p i ∘ x)).seq j.val) atTop (𝓝 0):=by
      let v:=trill x; choose c hc hA using hp; choose f hF using fun i=>yolk (p i) v (h i); let u:= Finset.range (2*k+1); let R:ℕ→ℝ:= Nat.cast; have hG:Set.InjOn R u:=Nat.cast_injective.injOn
      let V(i):= _root_.Lagrange.basis u R i; let H(i)(x:ℝ):= (V i).eval x; let A(i s):= p i (v.atK (R s)); let T(i): Token:=trill (H i)
      have hT(i): f i= _root_.Lagrange.interpolate u R (A i):= by
          have hi:= frontage K _ _ _ (hc i) (hA i) _ (f i) (hF i); apply _root_.Lagrange.eq_interpolate_of_eval_eq; exact hG
          · apply lt_of_le_of_lt hi; unfold u; rw [Finset.card_range]; exact_mod_cast (Nat.lt_succ_self (2*k))
          exact fun j _=> hF ..
      have he(i): trill (p i ∘ x)=∑ j∈u,plainJ (A i j)*T j:=by
          rw [thighs x hx (p i) (h i), show (p i∘ (trill x).atK)= (∑ j∈u,(fun _:ℝ=> A i j)*H j) from ?_]; exact Gael.chooses <| Stranded.nit _ _ _ fun j _=>(Reads.constants (A i j)).pile (Gael.oath (polGlass (V j)))
          funext x; change p i (v.atK x)= _; simp only [←hF (i:=i) x,hT i,_root_.Lagrange.interpolate_apply, Polynomial.eval_finsetSum,eval_mul,eval_C, H,V, Finset.sum_apply,Pi.mul_apply]
      simp_rw [he,Char.seqSum, JetS.plain_full]; simpa only [Finset.sum_const_zero] using! (tendsto_finsetSum u (fun j' _=> (show Tendsto (fun i:ℕ=> JetS.seq (A i j' • T j') j.val) atTop (𝓝 0) from by have h:= (ht (v.atK (R j'))).mul_const ((T j').seq j.val); simp only [zero_mul] at h; fin_cases j<;> exact h)))
-- subtract
lemma recoil (i:Phase)(f g:Token):(f-g).seq i.val=f.seq i.val-g.seq i.val:=by fin_cases i<;>change _ + -_ = (_:ℝ)- _<;> ring_nf <;> rfl
-- Sigma equality limit sums
omit [MeasurableSpace E][BorelSpace E] in
lemma impax (K:E→L[ℝ] F)(p:ℕ→ScriptJ E)(q:ScriptJ E)(h:∀ i,(p i).B)(hp:q.B)(k:ℕ)(hr:∀ i j, ∃ c:ℝ,0≤c∧∀ x:E, ‖((p i x).seq (j:Phase).val) -(q x).seq j.val‖ ≤ c*(1+‖K x‖)^k)(hv:∀ x:E,forall j:Phase,Tendsto (fun i=> (p i x).seq j.val) atTop (𝓝 ((q x).seq j.val)))(x:ℝ→E)(hx:Gael x)(j:Phase): Tendsto (fun i=> (mine (p i ∘ x)).seq j.val) atTop (𝓝 ((mine (q ∘ x)).seq j.val)):=by
          let f(i:ℕ)(a:Phase): E→ℝ:= fun z=> (p i z).seq a.val; let g(a:Phase):E→ℝ:= fun z=>(q z).seq a.val; let A(i a):=trill (f i a ∘ x); let B(a):=trill (g a ∘ x)
          have ha(i a):= Gael.oath (Gael.climb (f i a) (h i _) hx); have he(a):= Gael.oath (Gael.climb (g a) (hp _) hx)
          have ht(a b:Phase): Tendsto (fun i=> (A i a).seq b.val) atTop (𝓝 ((B a).seq b.val)):=by
                let t(i):=f i a-g a; have h1(i):Bond (t i):= (Bond.sub (h i _) (hp _)); have hq(i): trill (t i∘x)=A i a-B a:=Gael.chooses ((ha i a).minus (he a)); have hl(y:E): Tendsto (fun i=> t i y) atTop (𝓝 0):=by simpa only [sub_self] using! ((hv y a).sub (tendsto_const_nhds (x:= (q y).seq a.val)))
                have h' := pears K t h1 k (fun i=>hr i a) hl x hx b; apply (tendsto_sub_nhds_zero_iff).mp; simpa only [hq,recoil] using! h' -- recoil binder fix
          simp_rw [show ∀ i:ℕ,mine (p i ∘ x)=assembleJ (A i 0) (A i 1) (A i 2) from fun i=> Fitted.totals (p:=p i ∘ x) (ha i 0) (ha i 1) (ha i 2), show mine (q ∘ x)=assembleJ (B 0) (B 1) (B 2) from Fitted.totals (p:= q ∘ x) (he 0) (he 1) (he 2)]; fin_cases j <;> simp only [assembleJ, JetS.seq,pl_s,pl_l,pl_h,ml_h,ml_l,ml_s,Fin.isValue,ski] -- manually
          all_goals norm_num
          · exact ht 0 0
          · exact (ht 0 1).add (ht 1 0)
          exact ((ht 0 2).add (ht 1 1)).add (ht 2 0)
end Essay
end YM.OPE.Libra
