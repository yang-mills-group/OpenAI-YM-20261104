import YM.XSpace.Swatch
import YM.XSpace.Handle

/-!
# Transport first-order total density into the Chart. Applications of JetGauge
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open Function Module JetGauge Source Source.Drops Labels Lattice RG Wilson Next.Rank.Normal
open Finsupp PowerSeries
open scoped Topology BigOperators
variable {G:Gauge} {R:Period} (T:R.Tree)
abbrev RealDual := Module.Dual ℝ (R.Bonds → G.Color)
def reading (i:Roller R G): RealDual (R:=R) (G:=G) := (innerₗ G.Color (basisC G i.2)).comp (LinearMap.proj i.1)
lemma reading_at (A:R.Bonds→G.Color) (i:Roller R G): reading i A=A i.1 i.2:=by change inner ℝ (basisC G i.2) (A i.1)=_; rw [EuclideanSpace.basisFun_inner]

def woven (j:Roller R G): Knobs T G→₀ℂ:= ∑ i, Finsupp.single i (reading j (route T (axisB T G i)):ℂ)
abbrev Lift := exchange (woven T (G:=G))
abbrev readAt (u:Carrier T G):= Taylor.evalAt (axisB T G) u
abbrev twig (u:Carrier T G) (i:Knobs T G):ℂ:= (axisB T G).repr u i
lemma woven_read (u:Carrier T G): reads (woven T) (twig T u)=numbers (route T u):=by
  funext i; simp only [reads,woven,map_sum,linearCombination_single, twig,smul_eq_mul]
  conv_rhs=>unfold numbers; rw [← reading_at,← (axisB T G).sum_repr u]; simp only [map_sum,map_smul, Complex.ofReal_sum, smul_eq_mul, Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _=> mul_comm ..
lemma woven_at (u:Carrier T G) (p:St (Per R.side) G): readAt T u (Lift T p)=pit (route T u) p:=by
  change MvPolynomial.aeval (twig T u) _=_; rw [Lift,reads_val,woven_read]; rfl
lemma slit_twig (u:Carrier T G) (p:St (Per R.side) G): slit (twig T u) (Lift T p)=Lift T (D (route T u) p):=by rw [Lift,exchange_slit,woven_read]
lemma derivative_lift (i : Knobs T G) (p:St (Per R.side) G): δ i (Lift T p)= Lift T (D (route T (axisB T G i)) p):=by
  unfold δ; rw [show Legs.choose_var i 1=twig T (axisB T G i) from ?_,slit_twig]
  funext j; by_cases h:j=i; simp only [Basis.repr_self,Finsupp.single_eq_same,Complex.ofReal_one,h,Legs.chosen_eq,twig]
  rw [Legs.chosen_ne h]; dsimp only [twig]; rw [Basis.repr_self,Finsupp.single_eq_of_ne h, Complex.ofReal_zero]
lemma read_block (u:Carrier T G) (f:Module.Dual ℝ (Carrier T G)): readAt T u (JetGauge.Setup.block (fun i=> (f (axisB T G i):ℂ)))= ↑(f u):=by
  rw [Setup.block,_root_.map_sum]; simp only [readAt,Taylor.evalAt,map_smul,MvPolynomial.aeval_X, smul_eq_mul]; conv_rhs=>rw [← (axisB T G).sum_repr u,map_sum,Complex.ofReal_sum]; simp only [map_smul,smul_eq_mul,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _=>mul_comm ..
lemma read_shift (x:Carrier T G) (i j:Knobs T G): readAt T x ((guiding T G).shift (leanB T G) i j)= twig T (later T i x) j := read_block T x ((axisB T G).coord j ∘ₗ later T i)
lemma read_row (x:Carrier T G) (i:Knobs T G): readAt T x ((guiding T G).row i)=↑(spaceCharge T G (axisB T G i) x):= read_block T x (spaceCharge T G (axisB T G i))

def Good (A:PowerSeries (St (Per R.side) G)): Prop := (∀ v, D (grad v) (constantCoeff A) =0) ∧ ∀ v, ∀ u:R.Bonds→G.Color,pit u (D (grad v) (coeff 1 A))= -pit u (D (rLink v u) (constantCoeff A))
-- actual total inputs included in Good
lemma good_toy {d:ℕ} {H:Hol G} (S:Survey G H d) (x:R.Sites) (p:Label G d): Good (R:=R) (toy S x p.val):= ⟨quench S x p.val,fun v u=> pit_ward S x p u v⟩
lemma good_one (R:Period) (G:Gauge): Good (R:=R) (1: PowerSeries (St (Per R.side) G)):= by constructor <;> intros <;> simp
lemma good_mul {A B:PowerSeries (St (Per R.side) G)} (h:Good (R:=R) A) (g:Good (R:=R) B): Good (R:=R) (A*B):=by
  refine ⟨fun v=>?_,fun v u=>?_⟩
  · rw [map_mul, Derivation.leibniz,h.1,g.1]; simp
  rw [coeff_one_mul,map_add, map_mul constantCoeff,Derivation.leibniz,Derivation.leibniz,Derivation.leibniz]; simp only [h.1,g.1,map_add,smul_eq_mul,mul_zero,zero_add,map_mul,h.2,g.2]; ring
lemma good_list {Z : Type*} (s:Finset Z) (p:Z→PowerSeries (St (Per R.side) G)) (h:∀ i∈s, Good (R:=R) (p i)): Good (R:=R) (∏ i∈s,p i):=by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact good_one _ _
  | insert i s hi ih => rw [Finset.prod_insert hi]; exact good_mul (h _ (Finset.mem_insert_self ..)) (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))

def price1 (X : PowerSeries (St (Per R.side) G)):= coeff 1 X - cubic R G * constantCoeff X
lemma gauge_price1 (x: Carrier T G) (i:Knobs T G): pit (route T x) (D (grad (born T (axisB T G i))) (cubic R G))= -↑(spaceCharge T G x (later T i x)):=by
  rw [cubic,Derivation.map_smul,map_sum, map_smul,map_sum,spacelike]; simp_rw [price_ward,route_r]; push_cast; rw [Finset.sum_neg_distrib]; ring
lemma relay_shift (v x:Carrier T G) (p): readAt T x (slit (twig T v) p)= ∑ i, twig T v i * readAt T x (δ i p):=by rw [whole, map_sum]; exact Finset.sum_congr rfl fun i _=> map_smul (readAt T x) _ _
lemma relay_row (v x:Carrier T G) : (∑ i, twig T v i * readAt T x ((guiding T G).row i))=↑(spaceCharge T G x v):=by
  conv_rhs=>rw [← (axisB T G).sum_repr v,map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _=> ?_; rw [read_row,_root_.map_smul,smul_eq_mul,Complex.ofReal_mul]; rw [charge,charge,T.symmetric]

lemma ambient (X : PowerSeries (St (Per R.side) G)) (h:Good (R:=R) X) : (guiding T G).Room (leanB T G) (Lift T (constantCoeff X)) (Lift T (price1 (R:=R) X)):=by
  let Y:=Lift T (constantCoeff X)
  have he : (guiding T G).Centered Y:=fun i hi=>by rw [show Y=_ from rfl, derivative_lift T i,under T i hi,h.1,map_zero]
  refine ⟨he,fun i hi=>?_⟩; apply Taylor.from_real (axisB T G); intro u
  change readAt T u (δ i _) = readAt T u (∑ k, _)
  rw [derivative_lift T i,under T i hi,woven_at,price1,map_sub,Derivation.leibniz,h.1]; simp only [smul_eq_mul,mul_zero,zero_add, map_sub,map_mul,h.2,map_sum,read_shift]; rw [gauge_price1, ← relay_row T]
  have h2 : pit (route T u) (D (rLink (born T (axisB T G i)) (route T u)) (constantCoeff X))= readAt T u (slit (twig T (later T i u)) Y):=by rw [show Y=_ from rfl,slit_twig,woven_at,route_r]
  rw [h2,← woven_at,relay_shift]; simp_rw [mul_sub,Finset.sum_sub_distrib]; rw [mul_neg, neg_sub_neg,Finset.mul_sum]; unfold Y; congr 1; apply Finset.sum_congr rfl; intro i _; ring
end YM.XSpace.Chart2
