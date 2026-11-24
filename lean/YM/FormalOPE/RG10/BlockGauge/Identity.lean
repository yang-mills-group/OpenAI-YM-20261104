import YM.FormalOPE.RG10.BlockGauge.District
import YM.FormalOPE.RG10.BlockGauge.Sky
/-!
 # Using real auxiliary integrals for genuine diagrams (no physical report).

 Origin root truss gauge correspondence for any gauge invariant observable.
 Implement joint aux formal unnormalized evaluation defined independently at fixed regulator & fixed real weights.
 Ancillary Fubini identities for hierarchy and full product.
 This file poses real integral on positive weights. `v` allows schedule with total price coefficients
 e.g. inverse squared. Their jets are cost-schedule independent formal symbols; they are NOT the
 formal coupling itself.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.BlockGauge
open Filter Topology Function MeasureTheory PertExtension PertExtension.Orb Lattice RG
open InversionWard Push.Loops
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
namespace Fabric
variable (L : Fabric G n)
 def prepare (w:L.Accounts→ℝ)(f:L.LinksOn→ℝ)(x:L.LinksOn):= f x * Real.exp (- L.spend w x)
 def splitFee (w:L.Accounts→ℝ)(u:LinkFrame G n): ℝ:= Real.exp (- (w none * wilson u))
lemma income_expr (w:L.Accounts→ℝ)(u:L.LinksOn):
 Real.exp (- L.spend w u) = splitFee L w (L.principal u) * (L.thermostat (w ∘ some) * L.bright (w ∘ some) u):= by unfold splitFee bright; rw [L.budget_sum,neg_add,Real.exp_add,mul_div_cancel₀]; exact (L.thermostat_pos _).ne' -- check orientation

-- large chart. Require measurable bounded finite observable, maybe on chart later.
structure Reading (F:L.LinksOn→ℝ): Prop where
 meas : Measurable F
 bounded : ∃ C:ℝ,∀ x, ‖F x‖≤ C
 leg (p:Vertex n→ G.El): p L.loom.origin=1 → ∀ u, F (L.loom.spin p u)= F u
lemma licensed {f:L.LinksOn→ℝ}(hf:L.Reading f){w:L.Accounts→ℝ}(hw:∀ a,0<w a) : L.Reading (L.prepare w f) where
 meas := hf.meas.mul (Measurable.exp (L.measurable_cost w).neg)
 bounded := by
    obtain ⟨C,h⟩:= hf.bounded
    refine ⟨C,fun u=>?_⟩
    unfold prepare; rw [norm_mul, Real.norm_eq_abs (Real.exp ..), abs_of_pos (Real.exp_pos _)]
    exact (mul_le_of_le_one_right (norm_nonneg _) (by grw [neg_nonpos.mpr (L.nonneg_cost hw _)]; exact le_of_eq (Real.exp_zero))).trans (h _)
 leg p h u:= by unfold prepare; rw [L.invariant_cost,hf.leg p h]
lemma reads {f:L.LinksOn→ℝ}(h:L.Reading f): Integrable f L.always:= by
 obtain ⟨x,hx⟩:=h.bounded
 exact (integrable_const x).mono' h.meas.aestronglyMeasurable (Filter.Eventually.of_forall hx)
-- useful conditional interface for Mark.Read. ℝ (complex by splitting)
 def provision (w:L.Accounts→ℝ)(f:L.LinksOn→ℝ):= ∫ x,L.prepare w f x ∂L.always
variable (T:L.loom.Truss)
 def review (w:L.Accounts→ℝ)(F:(T.Bulk→G.El)→ℝ):= ∫ x, F x * Real.exp (- L.spend w (T.board x)) ∂Chart.physical G T.Bulk
lemma control {f:L.LinksOn→ℝ}(hf:L.Reading f) {w:L.Accounts→ℝ}(hw:∀ a,0<w a): L.provision w f = L.review T w (f ∘ T.board):= by
 have ht:= L.licensed hf hw
 exact T.elimination G.probHaar (L.prepare w f) (L.reads ht) ht.leg
lemma full_integral {f:L.LinksOn→ℝ}(hf:L.Reading f){w:L.Accounts→ℝ}(hw:∀ a, 0<w a):
 L.provision w f= L.thermostat (w ∘ some) * ∫ u:LinkFrame G n, L.splitFee w u * (∫ y, L.bright (w ∘ some) (L.combine u y) * f (L.combine u y) ∂L.later) ∂(now G n):= by
 unfold provision
 rw [← L.spread_packs.integral_comp' (L.prepare w f), integral_prod _ (show Integrable (fun u=> L.prepare w f (L.spread.symm u)) ((now G n).prod L.later) from L.spread_packs.integrable_comp_of_integrable (L.reads (L.licensed hf hw))), ← integral_const_mul]
 refine integral_congr_ae (Filter.Eventually.of_forall fun u=>?_)
 dsimp only; rw [←integral_const_mul,←integral_const_mul]; refine integral_congr_ae (Filter.Eventually.of_forall fun i=> ?_)
 dsimp only; rw [L.symm_eq]; unfold prepare; rw [income_expr,principal_comb]; ring

-- particularly top observable. port to Orb.expectation (only with top coefficient 1/t^2)
variable (h:LinkFrame G n→ℝ) (w:L.Accounts→ℝ)
lemma top_charge (hf:L.Reading (h ∘ L.principal))(hp:∀ i, 0<w i):
 L.provision w (h ∘ L.principal) = L.thermostat (w ∘ some) * ∫ u:LinkFrame G n,L.splitFee w u * h u ∂(now G n):= by rw [L.full_integral hf hp]; simp_rw [Function.comp_apply, principal_comb,integral_mul_const, normalized_assembly,one_mul] -- composition also w ∘ some!
lemma house : L.Reading (1:L.LinksOn→ℝ) where
 meas:=measurable_const
 bounded:=⟨1,fun _=> by simp⟩
 leg _ _ _:=rfl
 def balanced (w:L.Accounts→ℝ)(O:L.LinksOn→ℝ):= L.provision w O / L.provision w 1
lemma top_kept (hf:L.Reading (h ∘ L.principal))(hp:∀ i,0<w i): L.balanced w (h ∘ L.principal) = (∫ u,L.splitFee w u * h u ∂(now G n))/(∫ u,L.splitFee w u ∂(now G n)):= by
 unfold balanced; rw [L.top_charge h w hf hp]; have ho:= L.top_charge 1 w L.house hp; simp [Function.comp_def] at ho; change L.provision w 1= _ at ho; rw [ho]; exact mul_div_mul_left _ _ (L.thermostat_pos (w∘some)).ne'
end Fabric
end YM.FormalOPE.RG10.BlockGauge
