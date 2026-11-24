import YM.Pert.Triangle.Fans
import YM.Pert.First.Completion
/-!
The raw scalar and cubic field choices `uMinus, bFan` are homogeneous labels on the same radial Maxwell space; no gauge-variant field added. The sum over all axes carries the conventional half (unordered components are normalized by `Fans`), the pair mark an additional half and the cubic tensor the actual color bracket, without a coupling-dependent rescaling. At derivative order 0 every closed two-form jet is on shell; the chosen polynomial section really uses these representatives under projection.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Labels UVNext UVNext.FreeStress RawLabels Function Lattice Filter
open scoped Topology Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}
local notation "I3" => Fin 3

lemma onsite_raw (v : Labels.Taylor G 0) : rebase G 0 v=v := by
  let u := takeCurl v
  have hu : u ∈ onShell G.Color 0 := (show _ ∧ _ from ⟨closedCurl v, fun b w => Finset.sum_eq_zero (fun a _ => ?_)⟩)
  · let Q := (⟨u,hu⟩:Shell G 0)
    have h : gaugeJet Q=v := potential.injective (Subtype.ext (match_leg Q))
    exact h ▸ (show rebase G 0 (gaugeJet Q)=gaugeJet Q by rw [rebase,LinearMap.comp_apply, Extra.FD.sends_back])
  unfold grad Tensor.diagonal
  rw [show (fun z:E4=> (u a b) (fun _=>z))=(fun _=>(u a b) 0) from funext (fun x => congrArg _ (funext fun i : Fin 0=>i.elim0))]
  exact congrArg (fun p : E4→L[ℝ] G.Color=> p (basis a)) (congrFun (fderiv_const (E:=E4) (𝕜:=ℝ) (u a b 0)) w) -- D mismatch

def fanReading (h : Bool) (i : I3) : Labels.Taylor G 0 →ₗ[ℝ] G.Color := (2:ℝ)⁻¹ • (∑ a,∑ b, fan h i a b • component (initialPlace a b))
lemma reading_adjoint (v : Labels.Taylor G 0) (h i k) : fanReading h i (Labels.Taylor.paint k v) = G.adjoint k (fanReading h i v) := by simp [fanReading,map_sum,component_paint]
def fanLeg (h : Bool) (i : I3) (t : G.ColorIndex) : Pol G := MvPolynomial.C (2:ℂ)⁻¹ * ∑ a:Axis,∑ b:Axis,MvPolynomial.C (fan h i a b : ℂ) * mono (initialPlace a b) t
lemma read_fan (A : Jet G) (h i t) : Labels.read A (fanLeg h i t) = (↑(fanReading h i (A 0) t) : ℂ) := by
  simp only [fanLeg,fanReading, Labels.read, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self,RingHom.id_apply,map_sum, LinearMap.smul_apply,LinearMap.sum_apply,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,Complex.ofReal_mul,Complex.ofReal_inv, Complex.ofReal_ofNat,Complex.ofReal_sum,smul_eq_mul]
  congr 1; exact Finset.sum_congr rfl (fun _ _=> Finset.sum_congr rfl fun _ _=> congrArg _ (eval_mono _ t A))
lemma pure_fan (h i) (t : G.ColorIndex) : MvPolynomial.IsWeightedHomogeneous Labels.generation (fanLeg h i t) 2 :=
  (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun _ _=> MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun _ _=> (graded_mono _ t).C_mul _))).C_mul _
lemma fan_negate (h i) (t : G.ColorIndex) : YM.Pert.Parity.shadow G (fanLeg h i t) = -fanLeg h i t := eval_ext _ _ fun A=> by
  rw [YM.Pert.Parity.shadow_read,map_neg,read_fan,read_fan,Pi.neg_apply, map_neg,PiLp.neg_apply,Complex.ofReal_neg]
lemma joined_limit {R : Pol G} {w : ℕ} (h : MvPolynomial.IsWeightedHomogeneous Labels.generation R w) : R ∈ limited G w :=
   (MvPolynomial.mem_restrictSupport_iff ℂ).2 fun _ hb=> Nat.le_of_eq (h (MvPolynomial.mem_support_iff.mp hb))
lemma sum_color (v : G.Color) : ∑ c : G.ColorIndex,v c • unitColor G c=v := by
   ext i; rw [WithLp.ofLp_sum,Finset.sum_apply,Finset.sum_eq_single i]; all_goals simp_all [unitPaint,eq_comm]

def uMinus (G : Gauge) : Pol G := MvPolynomial.C (2:ℂ)⁻¹ * ∑ t:I3,∑ u:G.ColorIndex, fanLeg false t u ^ 2
lemma uMinus_cap : uMinus G ∈ Labels.limited G 4 :=
 joined_limit (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun i _=> MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun _ _=> pure_fan (G:=G) false i _ |>.pow 2)) |>.C_mul _)
lemma read_u (A : Jet G) : Labels.read A (uMinus G) = (2:ℂ)⁻¹ * ∑ t:I3, (↑(inner ℝ (fanReading false t (A 0)) (fanReading false t (A 0))):ℂ) := by
  unfold uMinus; rw [map_mul,show Labels.read A (MvPolynomial.C (2:ℂ)⁻¹)=_ from MvPolynomial.aeval_C ..,map_sum]; dsimp
  congr 1
  apply Finset.sum_congr rfl; intro t _
  let v := fanReading false t (A 0)
  have h:= EuclideanSpace.real_norm_sq_eq v
  rw [color_dot];simp [read_fan,Complex.ofReal_pow,Complex.ofReal_sum,sq]

def colorF (a b c : G.ColorIndex) : ℝ := inner ℝ (G.ad (unitColor G a) (unitColor G b)) (unitColor G c)
lemma bracket_expand (p q v : G.Color) : (∑ a,∑ b,∑ c,colorF a b c * (p a*q b*v c)) = inner ℝ (G.ad p q) v := by
  conv_rhs=> rw [←sum_color p,←sum_color q,←sum_color v]
  simp_rw [map_sum,LinearMap.sum_apply,LinearMap.map_smul,LinearMap.smul_apply,sum_inner,inner_sum, real_inner_smul_left,real_inner_smul_right, colorF]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun _ _=> Finset.sum_congr rfl (fun _ _=>Finset.sum_congr rfl fun _ _=>by ring))

def triple (t : I3 × I3 × I3) (a : G.ColorIndex × G.ColorIndex × G.ColorIndex) : Pol G := MvPolynomial.C (σ:=Labels.Key G) (↑(eps3 t.1 t.2.1 t.2.2) * ↑(colorF a.1 a.2.1 a.2.2):ℂ) * ((fanLeg true t.1 a.1) * (fanLeg true t.2.1 a.2.1) * (fanLeg true t.2.2 a.2.2))
lemma triple_pure (t) (a : G.ColorIndex × G.ColorIndex × G.ColorIndex) : MvPolynomial.IsWeightedHomogeneous Labels.generation (triple t a) 6 := (((pure_fan true t.1 _).mul (pure_fan true _ _)).mul (pure_fan true _ _)).C_mul _

def bFan (G : Gauge) : Pol G := ∑ i,∑ j,∑ k,∑ a,∑ b,∑ c,triple (i,j,k) (a,b,c)
lemma bFan_cap : bFan G ∈ limited G 6 := by unfold bFan; apply joined_limit; apply MvPolynomial.IsWeightedHomogeneous.sum; intro i _; apply MvPolynomial.IsWeightedHomogeneous.sum; intro j _; apply MvPolynomial.IsWeightedHomogeneous.sum; intro k _;apply MvPolynomial.IsWeightedHomogeneous.sum; intro u _;apply MvPolynomial.IsWeightedHomogeneous.sum; intro v _;apply MvPolynomial.IsWeightedHomogeneous.sum; exact fun a _ => triple_pure ..
lemma triple_value (A : Jet G) (i j k) (p q r : G.Color) (hi : p=fanReading true i (A 0)) (hq : q=fanReading true j (A 0)) (hw : r=fanReading true k (A 0)) : Labels.read A (∑ a,∑ b,∑ c,triple (i,j,k) (a,b,c))= (↑(eps3 i j k):ℂ)* (↑(inner ℝ (G.ad p q) r):ℂ) := by
  have he := congrArg ((↑):ℝ→ℂ) (bracket_expand p q r)
  push_cast at he
  rw [←he,Finset.mul_sum]; simp_rw [map_sum,triple,map_mul,read_fan,Finset.mul_sum]
  apply Finset.sum_congr rfl; intros _ _; apply Finset.sum_congr rfl; intros _ _; apply Finset.sum_congr rfl; intros _ _
  rw [hi,hq,hw]; simp [Labels.read]; ring
end YM.Pert.Triangle
