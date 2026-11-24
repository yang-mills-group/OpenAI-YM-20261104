import YM.X.Rank.Bump
import YM.Next.MAXWELL.Morsels
/-! Interpretation of the polynomial sampling under the given color convention. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Screen
open Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}
abbrev Sample (G : Gauge) := Style → G.Color
abbrev Mat (G : Gauge) := TileK G.ColorIndex
def coatV (q:Mat G) (A:Sample G) (v : Style) : G.Color:= WithLp.toLp 2 (q *ᵥ (A v).ofLp)
def helps (A:Sample G): WickPol G →ₐ[ℂ] ℂ := (aeval (fun k: Key G=> (A k.1 k.2 :ℂ))).comp (paint G)
lemma coat_one (A:Sample G):coatV 1 A=A:= by funext v; simp [coatV]
lemma coat_mul (P Q:Mat G)(A:Sample G) : coatV P (coatV Q A)=coatV (P*Q) A:= by funext v; simp [coatV,mulVec_mulVec]
lemma regularity (A:Sample G)(p:WickPol G) : ContDiff ℝ ∞ fun Q : Mat G=> helps (coatV Q A) p:= by
  unfold helps; simp only [AlgHom.comp_apply]; generalize paint G p=v
  induction v using MvPolynomial.induction_on with
  | C c => simp_rw [aeval_C]; exact contDiff_const
  | add p q h k => simp_rw [map_add]; exact h.add k
  | mul_X p i h=> simp_rw [map_mul, aeval_X]; apply h.mul; unfold coatV mulVec dotProduct; simp only [WithLp.ofLp_toLp,Complex.ofReal_sum]; refine ContDiff.sum fun j _=> ?_; refine Complex.ofRealCLM.contDiff.comp ?_; change ContDiff ℝ ∞ (fun x:Mat G=>x i.2 j*A i.1 j); exact ((Matrix.entryLinearMap ℝ ℝ i.2 j : Mat G →ₗ[ℝ] ℝ).toContinuousLinearMap.contDiff).mul contDiff_const
lemma foli (I:Type)[Fintype I] : Continuous (folio (J:=I) (V:=I)):= by unfold folio; fun_prop -- edit
private lemma send_star (p: Poly G) : realForm (send G p)=send G (MvPolynomial.map (starRingEnd ℂ) p) := by
  induction p using MvPolynomial.induction_on with
  | C c=> simp [send,realForm]
  | add p q h k=> simp only [map_add, h,k]
  | mul_X p i h=> rw [_root_.map_mul (send G), map_mul,h,send_X,realBit, map_mul (MvPolynomial.map _),MvPolynomial.map_X,_root_.map_mul (send G),send_X]
lemma helps_real (A:Sample G)(p: WickPol G): helps A (realForm p)=star (helps A p):= by
  have h (v:Poly G): helps A (realForm (send G v))=star (helps A (send G v)):= by
    rw [send_star]; simp only [helps,AlgHom.comp_apply,paintSend]; induction v using MvPolynomial.induction_on with
    | C c => simp
    | add p q h k => simp only [map_add,star_add,h,k]
    | mul_X p i h => simp only [map_mul, MvPolynomial.map_X,aeval_X, star_mul,h]; simp [Complex.star_def, mul_comm] -- edit
  rw [← sendPaint p]; exact h ..
lemma helps_invariant (A: Sample G) (p : WickPol G)(u:G.El): helps A (pigment u p)=helps (G.adjoint u ∘ A) p:= by
  rw [← sendPaint p]; generalize paint G p=v; induction v using MvPolynomial.induction_on with
  | C c=> simp [send,pigment, helps, paint]
  | add p q h k=> simp only [map_add,h,k]
  | mul_X p i h=>
    simp only [map_mul,h]; apply congr_arg
    rw [send_X,hue_orbit]; simp only [map_sum,map_smul,helps,AlgHom.comp_apply,paint_bit,penned,aeval_X]
    change (∑ j : G.ColorIndex,(G.adjoint u (unitColor G j) i.2:ℂ) • ((A i.1 j:ℝ):ℂ))=(G.adjoint u (A i.1) i.2:ℂ)
    conv_rhs => rw [← color_sum (A i.1),map_sum]
    simp only [map_smul, WithLp.ofLp_sum,Finset.sum_apply, Complex.ofReal_sum,PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]; exact Finset.sum_congr rfl fun i _=> mul_comm ..

lemma helps_filters (p q : WickPol G)(h:∀ A:Sample G, helps A p=helps A q) : p=q:= by
  apply full_poly; refine MvPolynomial.funext_set (fun _=> Set.range (fun x:ℝ=>(x:ℂ))) (fun _=> infinite_range_of_injective Complex.ofReal_injective) ?_
  intro X hx; choose Y hy using fun i:Key G=> hx i (mem_univ i); let A:Sample G:= fun v=> WithLp.toLp 2 fun j=>Y (v,j)
  rw [show X=fun i=> ((A i.1 i.2):ℂ) from (funext fun i=> (hy i).symm)]; exact h A
end YM.PositionX.Rank
