import YM.RegulatorIR.Cluster.Adapt

/-! Convenient shape-only adapter for fine eras: Zodiac1 and Zodiac2
payment at λ with extra residual exponents. Parameter of canonical discrepancy
allowed real; round up only AFTER sing width. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Ledger Ledger.Sky Ledger.Sky.Accounts Collapsed ENNReal
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W I Z: Type}{M:W→ℕ} {X Y:Page M→Type} {S: Sky X Y}{T:S.Accounts}{R:Composite I}
  {p e u r b n q:ℕ}{L:Meter W}{A:I→(w:Page M)→ Orders (X w)}
  {v:I→Page M→ℝ≥0∞}{D:I→ W→Set Room}{d:W→ℝ}{m H:I→ℕ}{σ:I→ℝ}{t:W→ℝ≥0∞}
  {c:Flap M→ℝ≥0∞}{x:W→Room}
namespace Composite
-- ε realizes costs

def loss (J:Composite I)(σ:I→ℝ):ℝ:=match J with
 | atom i=> σ i
 | pair A B=> A.loss σ+B.loss σ
lemma costpos (J: Composite I)(σ:I→ℝ)(h:∀ i,J.In i→0 ≤ σ i): 0≤ J.loss σ:=by induction J with
 | atom i=> exact h i rfl
 | pair A B ih ih'=> exact add_nonneg (ih (fun i hi=>h i (Or.inl hi))) (ih' (fun i hi=>h i (Or.inr hi)))
end Composite

def topGrowth (S:Sky X Y)(a:ℝ)(b:ℕ) (i:Page M) := (heightP S.l b i)⁻¹*ENNReal.ofReal ((S.ε i.bindW / S.l i)^a)
lemma factors (S:Sky X Y)(J:Composite I) (t: Page M) (σ:I→ℝ)(H:I→ℕ) : J.rent t (fun i=>topGrowth S (σ i) (H i))= topGrowth S (J.loss σ) (J.accounts H) t:=by
 have hp:= S.hl t; have he:0<S.ε t.bindW:= S.hl _; have Ht:0<S.ε t.bindW / S.l t:=div_pos he hp
 induction J with
 | atom i=>rfl
 | pair A B ih ih'=>
    change A.rent _ _*B.rent _ _=topGrowth S (_+_) (_+_) _; rw [ih,ih']; unfold topGrowth heightP; rw [pow_add, ENNReal.mul_inv,Real.rpow_add Ht, ENNReal.ofReal_mul (by positivity)]; exact mul_mul_mul_comm ..
    all_goals simp [hp]
-- upper bounds Pachy
structure Expanse (S:Sky X Y)(σ:I→ℝ)(D:I→W→Set Room)(J:Composite I)(d:W→ℝ)(x:W→Room)(L:Meter W):Prop where
 home : ∀ w, S.l w ≤ 1
 clear : ∀ w,0 < d w
 bound : ∃ r:W→ℝ,Poly L (fun w=>ENNReal.ofReal (r w)) ∧ ∀ w, 0 ≤ r w ∧ ∀ y∈area J D w,dist y (x w) ≤ r w
 scale : Poly (flapL M L) fun w=>ENNReal.ofReal (S.shift w)
 gap : Poly L fun w=>ENNReal.ofReal ((d w)⁻¹)
 budget : 0≤J.loss σ
namespace Expanse
variable (J:Composite I)(G:Expanse S σ D J d x L) (H:I→ℕ)
include G
lemma core : Zodiac L S (fun i=>topGrowth S (σ i) (H i)) D J d (J.accounts H) 1 x := by
 refine ⟨G.home,G.clear,G.bound,?_,G.scale,G.gap, by simp⟩
 apply Carry.mono (Carry.unit ..); intro w
 change J.rent w _ ≤ _; rw [factors]; unfold topGrowth
 apply mul_le_mul_right
 apply le_trans _ (show ENNReal.ofReal 1≤ 1 from ENNReal.ofReal_one.le)
 have hz:S.ε w.bindW ≤ S.l w:=S.heads w; have hp:= S.hl w; have h:0<S.ε w.bindW:=S.hl _
 exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one (by positivity) ((div_le_one hp).mpr hz) G.budget)
lemma improved (he:J.loss σ ≤ (b:ℝ)) : Zodiac L S (fun i=>topGrowth S (σ i) (H i)) D J d (J.accounts H+b) (fun w=> ENNReal.ofReal (S.ε w^J.loss σ)) x:=by
 refine ⟨G.home,G.clear,G.bound,?_,G.scale,G.gap,fun _=> ENNReal.ofReal_ne_top⟩
 apply Carry.mono (Carry.unit ..); intro w; dsimp only; rw [factors]
 have ht:=S.hl w; have hp:= G.home w; have hz:0<S.ε w.bindW:=S.hl _
 unfold topGrowth heightP; rw [Real.div_rpow hz.le ht.le, ENNReal.ofReal_div_of_pos (by positivity),pow_add,ENNReal.mul_inv, div_eq_mul_inv]
 · rw [← mul_assoc, mul_right_comm (c:=(ENNReal.ofReal (S.l w ^ J.loss σ))⁻¹)]; apply mul_le_mul'; apply mul_le_mul_right
   apply ENNReal.inv_le_inv.mpr; rw [← ENNReal.ofReal_pow ht.le,← Real.rpow_natCast]
   exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge ht hp he)
   exact le_rfl
 all_goals simp [ht]
end Expanse
end YM.RegulatorIR.Cluster
