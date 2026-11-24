import YM.MS.ScaleForest.CostOps
/-!
# Estimates for the pinned radial-scale integration

Use relative time (translated from retained scale). At this stage, UV limit
requires no compensation since these branches have at least two pins and
are already off the contact loci. We prove the convergence and estimates
needed to keep them in arbitrary longer graphs, e.g. when this inclusion
comes from a polar subgraph's replacement. All external/kernel directions
in every test sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I E J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]
   [TopologicalSpace I] {v:J→ℝ} {a b c d R:ℝ} {X:Curtain G I} {p:ℤ}
   {m:ℕ}

def velocity (F:Curtain G I)(z:ℂ)(x:I)(s t:ℝ):= plow 0 t (F z (s+t) x)
def vertical (F:Curtain G I) : Curtain G I:= fun z s x=> mend (velocity F z x s) 0

omit [FiniteDimensional ℝ E] in
theorem massive (W:Touch G m E) : (W.length:ℤ) ≤ mass W := by
   induction W with
   | nil=> simp [mass,fieldDim]
   | cons i W ih=> 
     rcases i with ⟨i,x⟩; rw [Price_cons,List.length_cons]; have hp:1≤ wfield i:= by rcases i.1.2.eq_false_or_eq_true with h|h <;> simp [wfield,dim,h]
     change _≤ wfield i +_; omega

-- positive exterior mass buys decay even when no loop phase is helping.
variable {F:J→Mob G} (W:Touch G m E) (A:J→ℝ)

theorem reserveAmount (h : fell 0 A F) (hp : a ≤ (mass W:ℝ)) (hx : ∀ i,v i≤0) :
    veg 0 (fun i=> fieldVal (plow 0 (v i) (F i) m) W) (fun i=> exp (a*v i)*A i) := by
   have he:= limitF (h m E W) hx; let S:= 0+(mass W:ℂ)
   have hw : scaleC 0 (fun i=> exp (a*v i)) (fun i=>‖amount S (v i)‖) := by
     refine ⟨1,zero_lt_one,0,fun i p hv=>?_⟩; dsimp only; rw [amount_norm]; simp only [S,pow_zero,one_mul,zero_add,Complex.intCast_re]; exact exp_monotone (mul_le_mul_of_nonpos_right hp (hx i))
   convert! Costs.mul (Rock.at_rate (E:=E) hw) he using 1; exact funext fun i=> funext fun p=> s_p_vector ..

-- easy pay full always, or require positive rank.
theorem reserveAny (h : fell 0 A F) (hx : ∀ i,v i≤0) : fell 0 A (fun i=> plow 0 (v i) (F i)) := by
   intro m E _ _ _ w
   have he : 0 ≤ mass w:= by have hv:=massive w; omega
   simpa only [zero_mul,Real.exp_zero,one_mul] using reserveAmount (F:=F) w A h (show (0:ℝ) ≤ (mass w:ℝ) by exact_mod_cast he) hx

theorem reservePositive (h : fell 0 A F)(hh:∀ i,Goods p (F i)) (hz:p≠0)(hx : ∀ i,v i≤0):
    fell 0 (fun i=>exp (v i)*A i) (fun i=> plow 0 (v i) (F i)) := by
   intro m E _ _ _ w; by_cases hK : w.length=0
   · have hv (i) : Goods p (plow 0 (v i) (F i)):= need_rank.walk _ _ (hh i); unfold fieldVal; simp_rw [show ∀ i x, plow 0 (v i) (F i) m (sail w x)=0 from fun i x=>ranks_off (hv i) _ (by simp [hK,hz.symm]) ]; exact Costs.zero fun i _ _=> mul_nonneg (Real.exp_pos _).le (znon h i)
   have he : 1≤ mass w:= by have he:= massive w; omega
   simpa only [one_mul] using reserveAmount (v:=v) w A h (show (1:ℝ) ≤ (mass w:ℝ) by exact_mod_cast he) hx

-- When a + b ≥ 0, global coarse exponential budgets
variable (h : Envelope R a b X) (ha : 0 ≤ a+b)
include h ha
omit [TopologicalSpace I] in
theorem priceUVvel {v:J→ℝ}(hv:∀ i,v i≤0) (s:J→ℝ)(z:J→disc R)(i:J→I): fell 0
    (fun j=> exp (a*s j)*exp (a*v j)) (fun j=> velocity X (z j) (i j) (s j) (v j)) := by
   have hh:= reserveAny _ (h J z (fun j=> s j+v j) i) hv
   refine pay_price hh zero_lt_one (fun j=>?_)
   rw [one_mul,← Real.exp_add,← mul_add]; unfold levy
   split <;> [exact le_rfl; rename_i h']
   exact exp_monotone (mul_le_mul_of_nonneg_right (by linarith : -b ≤ a) (le_of_not_ge h'))

theorem priceIRvel (hP:Waves R p X)(hz:p≠0)(s:J→ℝ){v:J→ℝ}(hv:∀ i,v i≤0) (z:J→disc R)(i:J→I): fell 0
    (fun j=> exp (-b*s j)*exp ((1-b)*v j)) (fun j=> velocity X (z j) (i j) (s j) (v j)) := by
   have hh:= reservePositive _ (h J z (fun j=> s j+v j) i) (fun j=> hP.funds _ (z j).property _ _) hz hv
   refine pay_price hh zero_lt_one (fun j=>?_)
   rw [one_mul,← exp_add,show -b*s j+(1-b)*v j= v j+-b*(s j+v j) from by ring, exp_add]; unfold levy
   split_ifs with hp <;> [exact mul_le_mul_of_nonneg_left (exp_monotone (mul_le_mul_of_nonpos_right (by linarith : -b≤ a) hp)) (exp_pos _).le; exact le_rfl]
end YM.MS.ScaleForest
