import YM.FormalOPE.RG10.MultiGauge.Tower
/-!
 # adjoined polynomial picture (true finite power-degree every coefficient)
 no inner product demanded on directions, use the full finite dimensional color /
 tree gauge model. Use linear polynomial tests for Sources (not homogenization of entire series).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MultiGauge
open Function Filter Topology Set MeasureTheory Measure PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {E F K : Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]
 [NormedAddCommGroup K][NormedSpace ℝ K]

def papers (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]: Subalgebra ℝ (E→ℝ):= Algebra.adjoin ℝ (Set.range fun a:Module.Dual ℝ E=> (a : E→ℝ))
abbrev Permit (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]:= ↥(papers E)
namespace Papers
lemma linear (a:Module.Dual ℝ E): (a:E→ℝ)∈ papers E:= Algebra.subset_adjoin ⟨a,rfl⟩
lemma fixed (x:ℝ): (fun _: E=> x)∈ papers E:= (papers E).algebraMap_mem x
lemma induction {P:(E→ℝ)→Prop} (l:∀ v:Module.Dual ℝ E,P v)(c:∀ x:ℝ,P (fun _=>x))
 (k:∀ f g:E→ℝ,f∈ papers E→g∈papers E→P f→P g→P (f+g))(s:∀ f g:E→ℝ,f∈papers E→g∈papers E→P f→P g→P (f*g)) {x:E→ℝ}(h:x∈papers E):P x:= by
 induction h using Algebra.adjoin_induction with
 | mem y hy=> rcases hy with ⟨x,rfl⟩; exact l x
 | algebraMap x=> exact c x
 | add => rename_i y z ha hb hw hf; exact k y z ha hb hw hf -- test
 | mul => rename_i y z ha hb hw hf; exact s y z ha hb hw hf

lemma consign (d:E→ₗ[ℝ] F)(v:F) {a:F→ℝ}(h:a∈ papers F): (fun x=>a (d x+v))∈ papers E:= by
 refine induction (P:=fun a:F→ℝ=> (fun x=>a (d x+v))∈papers E) ?_ (fun r=> fixed r) ?_ ?_ h
 · intro u; simp_rw [map_add]; exact (papers E).add_mem (linear (u.comp d)) (fixed (u v))
 · exact fun _ _ _ _ ha hb=> (papers E).add_mem ha hb
 exact fun _ _ _ _ ha hb=> (papers E).mul_mem ha hb

lemma pull (d:E→ₗ[ℝ] F) {a:F→ℝ}(h:a∈papers F): a∘d∈papers E:= by simpa [Function.comp_def] using consign d 0 h

variable [FiniteDimensional ℝ E]
lemma applies (a:Permit E): Continuous a.val ∧ Zone.Invoice (Radial.zone) a.val:= by
 refine induction (P:=fun f:E→ℝ=> Continuous f ∧ Zone.Invoice Radial.zone f) (fun ℓ=>(And.intro ℓ.continuous_of_finiteDimensional ?_)) ?_ (fun _ _ _ _ ha hb=> ⟨ha.1.add hb.1,ha.2.add hb.2⟩) (fun _ _ _ _ ha hb=> ⟨ha.1.mul hb.1,ha.2.mul hb.2⟩) a.property
 · exact Law.linearInvoice ℓ
 exact fun x=> ⟨continuous_const, Zone.Invoice.const x⟩

variable [MeasurableSpace E][BorelSpace E] (μ:Measure E)[IsAddHaarMeasure μ] (Λ: Law E)
lemma useful (a:Permit E): Integrable (a.val * Λ.kern) μ:= Λ.integrable_entry μ (applies a).2 (applies a).1
 def opening : Permit E →ₗ[ℝ] ℝ where
 toFun a:=Λ.average μ a.val
 map_add' a b:= by
    unfold Law.average; rw [show (a+b).val*Λ.kern= _ from (add_mul a.val b.val Λ.kern : (a.val+b.val)*Λ.kern=a.val*Λ.kern + b.val*Λ.kern )]; simp_rw [Pi.add_apply]; rw [integral_add (useful μ Λ a) (useful μ Λ b), add_div]
 map_smul' r a:= by unfold Law.average; change (∫ u:E,(r*a.val u)*Λ.kern u ∂μ) / _ = r*_; simp_rw [mul_assoc, Pi.mul_apply, integral_const_mul]; ring
lemma starts : opening μ Λ 1=1:= Λ.empty μ
end Papers
end YM.FormalOPE.RG10.MultiGauge
