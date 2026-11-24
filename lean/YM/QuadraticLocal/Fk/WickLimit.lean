import YM.Comparison.RG02.Bulk.Fk
/-!
# Legitimacy of Wick on assembled infinite unmasked kernel banks

Wick-limit interchange requires some justification. It's applied to finite-degree
polynomials, but they'd move in volume and support under the realtime weights.
 Only use this identity *at each fixed* volume before pricing the alias budget in a
 separate step. Thus no uniform momentum convergence bounds assumed. This reads the full
 `Order.observe` with mixed directions. Need convergence of all required input tensor
 entries; not even assuming a smooth barycenter independent of the true denominator.

 Use exactly `wordL`/`kernelJet`. In particular the relevant horizon of coherence
 after division is the coupling radius PLUS the maximum actual assigned `power` at any
 occurrence (which may be very high); all those orders' Taylor legs must agree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.WickLimit
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series
open Marker Multi Next.SectorChange
open Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order
open Extra.Trajectories (iteration connected)
open YM.Primitives.GCC.Anchor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {α E F G I V:Type}
variable [AddCommGroup E][Module ℂ E]
variable (L:Filter α) {p q:α→ E} {a b:E}
/- weak finite-dimensional subspace representation.L no compactness assumptions. -/
inductive Lens (L:Filter α): (α→E)→ E→ Prop
| key (x:α→ℂ)(a:ℂ)(h:Tendsto x L (𝓝 a))(P:E): Lens L (fun i=> x i • P) (a • P)
| plus {x y:α→E}{a b:E} (h:Lens L x a) (hu:Lens L y b) : Lens L (fun i=> x i+y i) (a+b)
-- Floor long limits. mult for CommSemiring.Algebra
variable {L}
lemma Lens.static (a:E): Lens L (fun _=>a) a:= by simpa only [one_smul] using Lens.key (L:=L) (fun _=> (1:ℂ)) 1 tendsto_const_nhds a
lemma Lens.spi {F:Type}[AddCommGroup F][Module ℂ F](k:E→ₗ[ℂ] F)(h:Lens L p a): Lens L (fun i=>k (p i)) (k a):=by
 induction h with | key x a h P=> simp_rw [map_smul]; exact Lens.key x a h (k P) | plus h hp ih ih'=> simp_rw [map_add]; exact Lens.plus ih ih'
lemma Lens.scale (z:ℂ)(h:Lens L p a): Lens L (fun i=> z • p i) (z • a):=(by let L:= (z • LinearMap.id (R:=ℂ) (M:=E)); exact h.spi L) -- check args
lemma Lens.earn (c:Finset I) {f:I→α→ E} {g:I→ E}(hp:∀i∈c,Lens L (f i) (g i)): Lens L (fun x=>∑ i∈c,f i x) (∑ i∈c,g i) := by
 induction c using Finset.induction with | empty=> simp only [sum_empty]; exact Lens.static _ | insert i c h ih=> simp_rw [sum_insert h]; exact (hp i (Finset.mem_insert_self ..)).plus (ih (fun i hi=> hp i (Finset.mem_insert_of_mem hi)))
lemma sine (Φ:E→ₗ[ℂ]ℂ)(h:Lens L p a): Tendsto (fun i=> Φ (p i)) L (𝓝 (Φ a)) := by
 induction h with
 | key x a h P=> simp_rw [map_smul,smul_eq_mul]; exact h.mul_const _
 | plus h hp ih ih'=> simp_rw [map_add]; exact ih.add ih'
section
variable {R:Type}[CommRing R][Algebra ℂ R]{x y:α→R} {a b:R}
lemma Lens.productive (h:Lens L x a)(hu:Lens L y b): Lens L (fun i=> x i*y i) (a*b):= by
 induction h with
 | key x a h P=> induction hu with
                |key f b he Q=> simp_rw [smul_mul_smul_comm]; exact Lens.key _ _ (h.mul he) (P*Q)
                | plus h hp ih ih'=> simp_rw [mul_add]; exact ih.plus ih'
 | plus h hp ih ih'=> simp_rw [add_mul]; exact Lens.plus ih ih'
lemma Lens.brew {f:I→α→R} {g:I→R}(c:Finset I)(h:∀i∈c,Lens L (f i) (g i)): Lens L (fun x=>∏ i∈c,f i x) (∏ i∈c,g i) := by
 induction c using Finset.induction with | empty=> simp only [prod_empty]; exact Lens.static _ | insert i c h' ih=> simp_rw [prod_insert h']; exact (h i (Finset.mem_insert_self ..)).productive (ih fun _ ht=> h _ (Finset.mem_insert_of_mem ht))
end
section lift
variable [Fintype I][DecidableEq I] [Fintype V] [DecidableEq V]
open MvPolynomial Next.Rank
variable {c f:Side} {G:Gauge} {C: StepData c f}
set_option quotPrecheck false
open Comparison.RG02 Assembly
variable (k:ℕ) {J:Census V}
lemma forge {E:Type*} [NormedAddCommGroup E][NormedSpace ℝ E](p:E)(A:(I→ℝ)→ₗ[ℝ]E) (Q:α→ContinuousMultilinearMap ℝ (fun _ : Fin k=>E) ℂ)(Y :ContinuousMultilinearMap ℝ (fun _ : Fin k=>E) ℂ)(hq:∀ x,Tendsto (fun z=> Q z x) L (𝓝 (Y x))): Lens L (fun v=> Assembly.wordL p A (Q v)) (Assembly.wordL p A Y) := by
 unfold wordL; simp_rw [C_mul']; apply Lens.earn; intro i _; exact Lens.key _ _ (hq _) _
variable (p: Clip)(P:PathData G)(O:ChartRatio G)
variable (K: Comparison.RG02.Bulk.Kernel C p P O)(B: Forest C.ratio)
variable (U: α→ Bulk.Colors J G f)(U0:Bulk.Colors J G f)
variable (t:C.Choices)(x: Exterior.fieldDir G c 1)
local notation "M"=> Precision.Key B G
local notation "W"=> fieldDir G c 1
local notation "ν"=> (Board J k)
variable (hv:∀ i,(U i).vac=U0.vac)(hp:∀ i,(U i).power=U0.power)
variable (hY:∀ j n (x:Fin n→ Bulk.Joint C B (G:=G)), Tendsto (fun i=> iteratedFDeriv ℝ n ( Bulk.markFn C B (U i) j ) 0 x) L (𝓝 (iteratedFDeriv ℝ n (Bulk.markFn C B U0 j) 0 x)))
include L hv hp hY
local notation "τ"=> ( Bulk.stage K B x )
local notation "θ"=> Bulk.hinge (S:=C) B
local notation "ε" v:max j:max=> (Assembly.generator ( Bulk.stage K B x ) (Bulk.hinge B) (v).power (Bulk.markFn C B v) (Bulk.geometric K B t v) k j)
local notation "R_v"=> Geometric.Rem.No -- unused
omit L hv hp hY in
-- impacts hv.In.`. syntax says not allowed? use include later.
private lemma earth {v:α}(h:(U v).vac=U0.vac) : Bulk.geometric K B t (U v)=Bulk.geometric K B t U0:= by unfold Bulk.geometric Bulk.fee Bulk.supplement; rw [h]
lemma talent (j:Multi.Hot (Board J k)) : Lens L (fun v=> (ε (U v) j)) (ε U0 j):= by
 unfold Assembly.generator; dsimp only; simp_rw [ earth p P O K B U U0 t ( hv _ ),hp]
 split;
 next h=> apply Lens.scale; unfold Assembly.kernelJet; apply WickLimit.forge; intro x'; simp_rw [ _root_.smul_apply]; exact Tendsto.const_smul (hY (⟨_,h⟩:Hot J) _ x') _ -- parentheses.P
 next h=> exact Lens.static _
lemma survey : Tendsto (fun i=> Bulk.Fk K B t (U i) x k) L (𝓝 (Bulk.Fk K B t U0 x k)):= by
 apply tendsto_pi_nhds.mpr; intro i
 -- transparency change? `Poly _` not defin.eq semired`. 
 let R'(f:MvPolynomial (Precision.Key B G) ℂ): ℂ:=0; unfold Bulk.Fk Assembly.prescription Cloud.prescription; apply WickLimit.sine; unfold Cloud.integrand; apply Lens.earn; intro j _; apply Lens.brew; intro l hl; exact talent k p P O K B U U0 t x hv hp hY l
end lift
variable {c f:Side} [Fintype V][DecidableEq V]{J:Census V}
-- all continuous under supported. ratio computes Poly denominators inverseMass using finite nil even when unit.Not interpreting flexible.
lemma always_log : Continuous ( Extra.Trajectories.connected (R:=J) ) := by
 suffices h : ∀ k:ℕ,Continuous (fun p: Poly J=> Extra.Trajectories.iteration p k) from h (Fintype.card V)
 intro k; induction k with
 | zero=> exact continuous_const
 | succ k ih=> simp_rw [iteration]; apply ih.add; apply Continuous.sub (show Continuous (fun p:Poly J=>p) from continuous_id); unfold Poly.pass; fun_prop (disch:=assumption) -- intros ih parser
lemma always_pass : Continuous (Poly.pass (R:=J)):=by change Continuous (fun x=> Poly.pass x); unfold Poly.pass; fun_prop
lemma always_ratio {k:ℕ} : Continuous (Order.ratio (R:=J) (r:=k)):=continuous_id.mul (show Continuous (fun i:Grade J k=> YM.Primitives.GCC.Anchor.inverseMass (Order.denominator i)) from (by
  unfold inverseMass; exact (always_pass).comp ((always_log.comp (Order.bottom J k|>.toLinearMap.continuous_of_finiteDimensional)).neg))) -- defeq test
lemma always_marked {k:ℕ}:Continuous (Order.logMarked (R:=J) (r:=k)):= always_log.comp always_ratio
end YM.QuadraticLocal.WickLimit
