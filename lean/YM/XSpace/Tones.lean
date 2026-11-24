import YM.XSpace.Trinity
/-! # All-color prices and the real chiral columns -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chiral
open Function Set Filter Lattice Chart2 Maxwell Maxwell.Free Maxwell.Wick MvPolynomial Structure1 Normalize
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge} {d:ℕ}
def br (i j k:G.ColorIndex):= G.ad (basisC G j) (basisC G k) i
lemma inB (i j k:G.ColorIndex): ⟪basisC G i, G.ad (basisC G j) (basisC G k)⟫_ℝ= br i j k:= EuclideanSpace.basisFun_inner ..
lemma br_swap (i j k:G.ColorIndex):br i j k= -br i k j:=by unfold br; rw [skew_ad]; rfl
lemma br_turn (i j k:G.ColorIndex): br i j k=br j k i:=by rw [← inB,← inB, show ∀ A B:G.Color,inner ℝ A B=inner ℝ B A from fun a b => real_inner_comm b a, skew_ad (basisC G j), inner_neg_left,Gauge.ad_skew,neg_neg]
lemma br_diag (i j:G.ColorIndex):br i i j=0:=by rw [br_turn,br_turn]; have h:=br_swap j i i; linarith
lemma br_diff (i j k:G.ColorIndex)(h:br i j k≠0):i≠j∧j≠k∧i≠k:= by
  refine ⟨fun e=> h (e.symm ▸ br_diag ..),fun e=> h (e.symm ▸ ?_), fun e=>h (e.symm ▸ ?_)⟩
  · rw [br_turn, br_diag]
  rw [br_turn,br_turn,br_diag]
lemma br_price (x y:G.Color)(i:G.ColorIndex): (G.ad x y) i=∑ j:G.ColorIndex,∑ k:G.ColorIndex,x j*y k*br i j k:=by
  have he(x:G.Color): (∑ i:G.ColorIndex, x i • basisC G i)=x:=(basisC G).sum_repr x
  conv_lhs=> rw [← he x,← he y,map_sum G.ad,LinearMap.sum_apply]; skip
  simp only [WithLp.ofLp_sum,Finset.sum_apply, _root_.map_smul,LinearMap.smul_apply,PiLp.smul_apply, smul_eq_mul,map_sum]; simp only [br,mul_assoc]; exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> mul_left_comm ..
lemma br_inner (z x y:G.Color): ⟪z,G.ad x y⟫_ℝ=∑ i:G.ColorIndex,∑ j:G.ColorIndex, ∑ k:G.ColorIndex,x j*y k*br i j k*z i:=by simp only [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial,br_price, Finset.sum_mul]
def S_color (G:Gauge):ℝ:=∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex, br i j k^2
lemma color_positive (h:G.Simple): 0< S_color G:=by
  obtain ⟨x,y,h⟩:=h.nonabelian; by_contra hv; have ht : S_color G=0:= le_antisymm (le_of_not_gt hv) (by unfold S_color; positivity); apply h; ext1 i; rw [br_price]
  have hh {I:Type}[Fintype I](x:I→ℝ)(h:0≤x)(hx:(∑ i,x i)=0)(k:I): x k=0:= (Finset.sum_eq_zero_iff_of_nonneg (fun i _=> h i)).mp hx k (Finset.mem_univ _)
  have he (i j k:G.ColorIndex):br i j k=0:= sq_eq_zero_iff.mp (hh _ (fun _=>sq_nonneg _) (hh (fun j=>∑ k,br i j k^2) (fun j=> Finset.sum_nonneg fun k _=>sq_nonneg _) (hh (fun i=>∑ j,∑ k,br i j k^2) (fun i=> Finset.sum_nonneg fun j _=> Finset.sum_nonneg fun k _=>sq_nonneg _) ht i) j) k); simp [he]

abbrev Name (G:Gauge) := P × G.ColorIndex
def Fq (σ:Bool)(i:P) : Flavor 0 := ∑ b:PlaqAxes,q σ i (six b) (endr b) • cell (six b) (endr b)
def arm (σ:Bool)(i:Name G) := Maxwell.Free.flavor (G:=G) 0 i.2 (Fq σ i.1)
def spark (σ: Bool)(i: Name G):= symbol 0 (arm σ i)
abbrev plusV := spark (G:=G) true
abbrev minusV := spark (G:=G) false
def fuel (i j k: Name G):ℂ:= (↑(liftedSign i.1 j.1 k.1*br i.2 j.2 k.2):ℂ)
lemma fuel_real (i j k: Name G):star (fuel i j k)=fuel i j k:=RCLike.conj_ofReal ..
lemma turn_fuel (i j k:Name G): fuel i j k= fuel j k i:=by unfold fuel; rw [revolves i.1 j.1 k.1,br_turn i.2 j.2 k.2]
lemma swap_fuel (i j k:Name G): fuel i j k= fuel j i k:=by rw [turn_fuel i]; unfold fuel; rw [lift_swap,br_swap j.2 k.2 i.2,neg_mul_neg]
lemma fuel_diff (i j k:Name G)(h:fuel i j k ≠0):i.2≠j.2∧ j.2≠k.2 ∧ i.2≠k.2:=br_diff _ _ _ (fun g=>h (by simp [fuel,g]))
def B (G:Gauge): WickPol G:=∑ i:Name G,∑ j:Name G,∑ k:Name G, fuel i j k • (plusV i * plusV j * plusV k)
def U (G:Gauge): WickPol G:=(2:ℂ)⁻¹ • ∑ i:Name G, minusV i*minusV i
lemma light (σ:Bool)(i:Name G)(X:TaylorTower G): probe X (spark σ i)=↑((available (X 0) (Fq σ i.1)) i.2):= symbol_test ..
abbrev vₜ (i:P)(X:TaylorTower G) := available (X 0) (Fq true i)
lemma fuelled (X:TaylorTower G): probe X (B G)=∑ i:P,∑ j:P,∑ k:P,(↑(liftedSign i j k*⟪vₜ i X, G.ad (vₜ j X) (vₜ k X)⟫_ℝ):ℂ):=by
  simp only [B,map_sum,map_smul,map_mul, show plusV (G:=G)=spark (G:=G) true from rfl,light, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; simp_rw [Finset.sum_comm (s:=(Finset.univ:Finset G.ColorIndex)) (t:=(Finset.univ:Finset P))]; apply Finset.sum_congr rfl; intro k _; rw [br_inner]; simp only [Finset.mul_sum, fuel, vₜ,Complex.ofReal_sum,Complex.ofReal_mul,smul_eq_mul]; apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro e _; ring
lemma understand : U G=(2:ℂ)⁻¹ • ∑ i:P, team G (Fq false i) (Fq false i):=by unfold U; rw [Fintype.sum_prod_type];rfl
lemma B_grade : IsWeightedHomogeneous scaleW (B G) 6:= by unfold B; apply IsWeightedHomogeneous.sum; intro i _; apply IsWeightedHomogeneous.sum; intro j _; apply IsWeightedHomogeneous.sum; intro k _; apply (weightedHomogeneousSubmodule ℂ scaleW 6).smul_mem; exact ((symbol_hom (arm true (G:=G) i) (fun i=>i+2)).mul (symbol_hom (arm true (G:=G) j) (fun i=>i+2))).mul (symbol_hom (arm true (G:=G) k) (fun i=>i+2))
lemma U_grade : IsWeightedHomogeneous scaleW (U G) 4:= by unfold U; refine (weightedHomogeneousSubmodule ℂ scaleW 4).smul_mem _ ?_; apply IsWeightedHomogeneous.sum; intro i _; exact (symbol_hom (arm false (G:=G) i) (fun i=>i+2)).mul (symbol_hom (arm false (G:=G) i) (fun i=>i+2))
lemma B_paint : B G ∈ shellSector G 6:=by
  apply sector.mpr; refine ⟨?_,?_⟩
  · rw [lowerCap, mem_restrictSupport_iff]; exact fun _ hi=> (B_grade (MvPolynomial.mem_support_iff.mp hi)).le
  intro v; apply equalPol; intro X; rw [pigment_action,fuelled,fuelled]; simp only [vₜ,shade,shows_hue,← Show.adj_state,Show.shade_price]
end YM.XSpace.Chiral
