import YM.QuadraticLocal.Tariff.Warranty
import YM.QuadraticLocal.Tariff.Stamps
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tariff
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V W : Type} [DecidableEq V] [Fintype V][DecidableEq W][Fintype W]
variable (u:W→ V) (R: Census V) (o : V→Site n)
local notation "S"=> (Annuncia.Replica u R)
local notation "ϕ"=> ( Annuncia.Replica.bill u R )
variable (γ:(Replica u R).Mode→ℂ)
variable (w:V→ℝ)(hw:∀ i,0<w i)
variable {T J η : Type*} {a b c δ ε :ℝ}{B B' :ℕ}
local notation "ν"=> ( w ∘ u )
open Next.Foundations
variable {P:Rep G n} (L:Gallery T J o P R)(x:T) (h:L.Pays w a b c)
local notation "D"=> L.density x
include h hw
-- integrability (no HEIGHT estimate.V.Resource_inUse.Canvas. Only for commuting push WITHOUT assuming integrability of observer replies. Uses `hit` norms to evaluate, but does NOT use estimates after integration for local comparison.H_F_B.Struct.St.Memory`)
lemma gross (ha:0≤a)(he:RG.Envelope fun v=> Real.exp ( P.exponent v )) : ∃ e, ∀ v, ‖( D ) v‖ ≤ e := by
    obtain ⟨c',hc'⟩:= he.2; obtain ⟨k,hk,hK⟩:= Marker.Poly.equivalent_norm (R:=R) hw; obtain ⟨f,hf,hF,hδ⟩:= h.budget.budget; let E:= L.E; let x₁ (i:J):= Poly.toll w (E.mode i)*f i; let p0:= P.p; have hE0(v): Poly.price w (E.log x v) ≤ ∑' i,x₁ i:= by
        refine (Poly.budgeted hw (RG3.Letters.Frame.from_hit p0.B a b _ (fun i=> ⟨_, (L.E.address i).anchor⟩) (fun i=> mul_nonneg (Poly.worth hw _).le (hf i)) ha hδ).2.1 (fun i=> (?_: Poly.price w (E.frame i x v) ≤ x₁ i) ) ).2
        rw [Lamps.frame, Poly.solo]; exact (mul_le_mul_of_nonneg_left (Lamps.light_size E i x v ( hF i x _ (E.address i).anchor )) (Poly.worth hw _).le)
    obtain ⟨g,hg,hG⟩:= h.wages.wages; let x₂ i:= Poly.price w (g i); have ht : Summable x₂:= (RG3.Letters.Frame.from_hit p0.B a c x₂ (fun i=> ( (P.activities).forced i ).inventory_ne.mono ( (P.activities).forced i ).inventory_sup ) (fun i=> Poly.nonnegative hw _) ha hG).2.1
    let κ0 (s:Finset ℕ):= ∏ j∈s,x₂ j; have hz v: Poly.price w (L.gas x v) ≤ ∑' s,κ0 s:= by
        apply (Poly.budgeted hw (summable_finsetProd_of_summable_nonneg (fun i=> Poly.nonnegative hw _) ht) (fun i=> ?_)).2; unfold packet; split; next h => exact ( Poly.multiple hw .. ).trans (Finset.prod_le_prod (fun i _=> Poly.nonnegative hw _) (fun i _=> (hg i x v).reprice _ hw))
        next=> rw [Poly.zero_price]; exact Finset.prod_nonneg fun i _=> Poly.nonnegative hw _ -- maybe lean expected g
    refine ⟨ ( c' * (Real.exp (∑' i,x₁ i) * ∑' s,κ0 s) * k ),fun v=> (hK _).trans (mul_le_mul_of_nonneg_right ?_ hk)⟩
    let f:=L.gas x v; let t:= Poly.pass (E.log x v); unfold Gallery.density; rw [Marker.Poly.adapted]; refine mul_le_mul (show ‖( (Real.exp (P.exponent v)):ℂ )‖≤ c' from ?_) (( Poly.multiplication hw t f).trans ?_) (Poly.nonnegative hw _) (( norm_nonneg _ ).trans (hc' v))
    · rw [Complex.norm_real]; exact hc' v
    exact mul_le_mul ((Marker.Poly.pass_budget hw _).trans (Real.exp_le_exp.mpr (hE0 v))) (hz v) (Marker.Poly.nonnegative hw _) (Real.exp_pos _).le
variable [Countable J]
lemma measure (ha:0≤a)(he:RG.Envelope fun v=> Real.exp ( P.exponent v )) : Measurable (L.density x) :=by
    have hm: Measurable ( Complex.ofReal ∘ fun v=>Real.exp (P.exponent v)):= Complex.continuous_ofReal.measurable.comp he.1
    refine hm.smul ((Poly.pass_cont.measurable.comp (.tsum (f:=fun i v=>L.E.frame i x v) ?_)).mul (.tsum (f:=fun i v=>packet P.activities P.p (L.K.hard x) v i) ?_) ) -- implicit f
    · intro i; apply ( Overlay.Bands.sends _ ).measurable.comp; unfold Lamps.light; split; exact ( L.E.legal x i ).borel; exact masked_measurable _ _ _ ( L.E.legal x i ).borel -- namespace Overlay?
    intro i; unfold packet; exact Measurable.ite (P.activities.admissible_borel ..) (Finset.measurable_fun_prod _ fun i _=> (L.K.locality x i).borel ) measurable_const
lemma integrable {r s v t x':ℝ} (ha:0≤a)(he:P.Lawful r s v t x') : Integrable (L.density x) (prior G n):=by
    let hf:=( Rep.exponentEnv P he).exp; obtain ⟨c,hc⟩:= Tariff.gross R o w hw L x h ha hf; exact Integrable.of_bound (Tariff.measure R o w hw L x h ha hf).aestronglyMeasurable c ( Eventually.of_forall hc ) -- signatures
end YM.QuadraticLocal.Tariff
