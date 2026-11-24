import YM.OPE.Compatible.Lux.Amber
/-!
# Instrument the prices at sharp weights. Needed through cuts too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Table MeasureTheory Cov
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {L:Register G} {S:Table L} {P : DiffPlan S} {R : S.Rotation} {ρ : S.RealSpin}
  {l X X' Y:Type} [NormedAddCommGroup X][NormedAddCommGroup Y]{φ : Filter l} {T r s : l → ℝ} {d : ℕ}
-- use norm; product logic adjust m

def PaidWeight {X:Type}[Norm X] (φ:Filter l)(T r:l→ℝ)(f:l→X):= Score φ T (fun i=>r i*‖f i‖)
namespace PaidWeight
variable {f f':l→ X}{g:l→Y}
lemma alter (h:PaidWeight φ T r f)(he:f=ᶠ[φ] f'): PaidWeight φ T r f':= Score.congr h (by filter_upwards [he] with i hi; exact congr_arg (fun x:X=> r i*‖x‖) hi)
lemma ascaled [NormedSpace ℂ X](hp:∀ᶠ i in φ,0 ≤ r i): PaidWeight φ T r f ↔ Score φ T (fun i=> (r i:ℂ) • f i):=by
    have hh:∀ᶠ i in φ, ‖(r i:ℂ) • f i‖=‖r i * ‖f i‖‖ := hp.mono fun i hi=>by simp only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hi,Real.norm_of_nonneg (mul_nonneg hi (norm_nonneg (f i)))]
    exact ⟨fun h=> Score.liftp h (hh.mono fun i hi=> hi.le),fun h=> Score.liftp h (hh.mono fun i hi=>hi.ge)⟩
lemma applyLinear [NormedSpace ℂ X][NormedSpace ℂ Y] (h:PaidWeight φ T r f)(hs:∀ᶠ i in φ,0≤r i)(ht:Tendsto T φ atTop) (F:X→ₗ[ℂ] Y): Continuous F → PaidWeight φ T r (fun i=> F (f i)):=by
   intro hc; refine (ascaled hs).mpr (Score.congr (((ascaled hs).mp h).lift_l ht ({ toLinearMap := F.restrictScalars ℝ, cont:=hc} : X →L[ℝ] Y)) ?_); filter_upwards with i; exact F.map_smul _ _
lemma add [NormedSpace ℂ X](h:PaidWeight φ T r f)(hf:PaidWeight φ T r f')(hp:∀ᶠ i in φ,0≤ r i)(ht:Tendsto T φ atTop): PaidWeight φ T r (fun i=> f i+f' i):= (ascaled hp).mpr ((((ascaled hp).1 h).plus ((ascaled hp).1 hf) ht).congr (Eventually.of_forall fun _=>(smul_add ..).symm))
lemma sub [NormedSpace ℂ X](h:PaidWeight φ T r f)(hf:PaidWeight φ T r f')(hp:∀ᶠ i in φ,0≤ r i)(ht:Tendsto T φ atTop): PaidWeight φ T r (fun i=> f i-f' i):= (ascaled hp).mpr ((((ascaled hp).1 h).goes ((ascaled hp).1 hf) ht).congr (Eventually.of_forall fun _=>(smul_sub ..).symm))
lemma monoWeight (h:PaidWeight φ T r f)(hs:∀ᶠ i in φ,0≤ s i)(he:∀ᶠ i in φ, s i ≤ r i): PaidWeight φ T s f :=by
   exact Score.pointwise h (he.mono fun _ h=> mul_le_mul_of_nonneg_right h (norm_nonneg _)) (hs.mono fun _ h=> mul_nonneg h (norm_nonneg _))
end PaidWeight
end YM.OPE
