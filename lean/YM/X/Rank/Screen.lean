import YM.X.Rank.Draw
/-! Arbitrary exponential weights on the Gram of the test-color matrix can be inserted;
this will permit seeing its complete compact orbit rather than just the radial projections. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank.Screen
open Function Set Filter Finsupp Maxwell Wick MeasureTheory Matrix
open YM.Next.SectorChange.Gaussian YM.Next.Rank.Normal MvPolynomial Heat
open scoped Topology BigOperators Classical Kronecker
variable {I A:Type}[Fintype I]

def shadow (v : I→ℝ)(x : Tile I):= ∑ i:I, ((folio x *ᵥ v) i)^2
def stamp (v : I→ℝ)(x:Tile I):= Real.exp (- shadow v x / 2)
@[fun_prop] lemma stamp_cont (v : I→ℝ): Continuous (stamp v) := by unfold stamp shadow folio Matrix.mulVec dotProduct; simp only [Matrix.of_apply]; fun_prop
lemma stamp_range (v : I→ℝ)(x:Tile I): 0<stamp v x∧stamp v x≤1:= by
  unfold stamp; exact ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Finset.sum_nonneg fun _ _=>sq_nonneg _)) zero_le_two)⟩
variable [DecidableEq I]
abbrev price (P : TileK I) := (1 ⊗ₖ P⁻¹ : TileK (I×I))
abbrev cloudP (P : TileK I) := cloud (price P)
def Mirrors (F : Tile I→ℂ): Prop:= ∀ P:TileK I,P.PosDef→ Integrable F (cloudP P) ∧ ∫ x,F x ∂cloudP P=0

variable {G : Gauge}{F W:Tile I→ℂ}

lemma clock (P : TileK I)(hp:P.PosDef)(x:Tile I): force (price P) x = ∑ i:I, folio x i ⬝ᵥ (P *ᵥ folio x i) := by
  rw [force,price,inv_kronecker,(show (1:TileK I)⁻¹=1 by simp), Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp.det_pos.ne')]; unfold dotProduct; rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun k _=>?_; apply congr_arg (x (i,k)*·)
  unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type]; simp only [kronecker_apply, one_apply, ite_mul,one_mul,zero_mul,← Finset.ite_sum_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]; rfl -- edit
lemma tall (P : TileK I)(hp:P.PosDef) : (price P).PosDef:=Matrix.PosDef.one.kronecker hp.inv
lemma added (P : TileK I)(hp:P.PosDef)(v:I→ℝ) : (P+ Matrix.vecMulVec v v).PosDef:= by
    apply hp.add_posSemidef; have h:=posSemidef_vecMulVec_self_star v; simpa using h
lemma frame_add (P : TileK I)(hp:P.PosDef)(x:Tile I)(v:I→ℝ) : force (price (P+ Matrix.vecMulVec v v)) x = force (price P) x + shadow v x := by
  rw [clock _ (added P hp v),clock P hp]; unfold shadow; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _
  rw [add_mulVec, dotProduct_add]; congr 1
  unfold dotProduct Matrix.mulVec dotProduct; simp_rw [vecMulVec_apply,mul_assoc,← Finset.mul_sum,sq, ← mul_assoc]; rw [← Finset.sum_mul]; congr 1; rw [show ∑ k : I,v k* folio x i k=_ from Finset.sum_congr rfl fun j _=> mul_comm (v j) _]

lemma shelter (P : TileK I)(hp:P.PosDef)(x:Tile I)(v:I→ℝ) : let Q:=P+ Matrix.vecMulVec v v
     ratio (price P) x * stamp v x= (coat (price P))⁻¹ * coat (price Q) * ratio (price Q) x := by -- ambiguous syntax coat (P⁻¹)?
  intro Q; simp only [ratio, frame_add P hp x v,Q, stamp]; have hp:= coat_pos (tall _ (added P hp v)); rw [neg_add, add_div,Real.exp_add]; have ht:=(coat_pos (tall P (by assumption))); field_simp

lemma cover_int {I:Type}[Fintype I][DecidableEq I]{P:TileK I}(hp:P.PosDef){W:Type*}[NormedAddCommGroup W][NormedSpace ℝ W](F:(I→ℝ)→W):
   (∫ x, F x ∂cloud P)=∫ x, ratio P x • F x := by
  rw [cloud_formula hp, integral_withDensity_eq_integral_toReal_smul]; simp_rw [fun x=>ENNReal.toReal_ofReal (ratio_pos hp x).le]; all_goals first|fun_prop|exact (measurable_ratio P).ennreal_ofReal|exact Filter.Eventually.of_forall (fun _=>by simp)
namespace Mirrors
lemma stamp_test (h:Mirrors F) (v:I→ℝ): Mirrors (fun x=>stamp v x • F x):= by
  intro P hp; let Q:=P+ Matrix.vecMulVec v v; obtain ⟨hl,hQ⟩:= h Q (added P hp v); obtain ⟨ht,-⟩:= h P hp
  refine ⟨ht.bdd_smul 1 (stamp_cont v).aestronglyMeasurable (Eventually.of_forall (fun x=> (Real.norm_of_nonneg (stamp_range v x).1.le).trans_le (stamp_range v x).2)),?_⟩
  rw [cover_int (tall _ hp)]; simp_rw [smul_smul, fun x=> shelter P hp x v]; simp_rw [mul_smul]; rw [integral_smul,integral_smul,← cover_int (tall _ (added P hp v)),hQ,smul_zero,smul_zero]
protected lemma plus (h:Mirrors F)(w:Mirrors W): Mirrors (F+W) := fun P hp=> ⟨(h P hp).1.add (w P hp).1,by simp only [Pi.add_apply]; rw [integral_add (h P hp).1 (w P hp).1,(h P hp).2,(w P hp).2,add_zero]⟩
protected lemma scales (h:Mirrors F)(x:ℂ): Mirrors (x • F):= fun P hp=>⟨(h P hp |>.1.smul x),by simp only [Pi.smul_apply]; rw [integral_smul,(h P hp).2,smul_zero]⟩
lemma fires {S:Finset E4}(p:Canvas G)(c:G.ColorIndex)(A:Stroke→G.Color)(hp:Fits S p)(hv:Silent c p S): Mirrors (fun x=>foul x p A):= by
  intro P h; refine ⟨?_,color_draw p A c hp hv P⁻¹ h.inv⟩
  simp_rw [← lens_v]; exact (pushPaid _ _ (tall _ h)).1
end Mirrors
end YM.PositionX.Rank.Screen
