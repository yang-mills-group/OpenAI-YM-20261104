import YM.FVA2.Press.Integrated
/-!
# Midpoint phase vs holonomy

The actual stencil uses link holonomy to test its jet, the MS bare coefficient tests
point-value input at a link MIDPOINT. For homogeneous plane waves, keep degree and pay lower
powers with the exact triangular binomial (integration along edge = polynomial). This way
componentwise highest-rank match works at all horizons; not just first plaquette weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press.Integration
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Plane MS.Tone MS.Native MS.Theater MS.Momentum
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {k d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "E" => tilt A
local notation "B" => GaugePanel G A.size
local notation "C" => G.Color
local notation "X" => Edge Cover
local notation "L" => Work.G03.castPos
section
variable (p:QP)(i:Axis)(x:Cover)
def beg := (embed x) + (1/2:ℝ) • embed (step i)  -- `args`
def mid_charge := pairing p (beg i x) -- params capture
lemma paired (p q:QP): pairing p q=inner ℝ (fixF p) (fixF q):= by unfold pairing; rw [PiLp.inner_apply]; exact sum_congr rfl (fun i _=> by rw [RCLike.inner_apply]; exact mul_comm (p i) (q i))
lemma center_point (t:ℝ) : inner ℝ (fixF p) (L x + t • basis i) = mid_charge p i x+ p i * (t-1/2):= by
 unfold mid_charge beg; rw [paired,map_add,map_smul]; simp only [inner_add_right,real_inner_smul_right,lean_axis]
 rw [show fixF (embed x)=L x from rfl, show fixF (embed (step i))=basis i from ?_,lean_axis]; ring
 ext j; rw [show fixF (embed (step i)) j=(if j=i then 1 else 0) from emb_step i j]; simp
end
section
variable (p:QP)(v:G.ColorIndex)(i:Axis)
local notation "e" => cl G v
def scatterM (k:ℕ)(x:X): C:= if x.2=i then amount k • ((mid_charge p x.2 x.1)^k • cl G v) else 0
private def frac (p:QP)(i:Axis)(k j:ℕ)(t:ℝ):= amount k * (Nat.choose k j) * (p i*(t-(1/2:ℝ)))^(k-j) / amount j
lemma pinPoint (k:ℕ)(x:X)(t:ℝ): Tensor.diagonal ((speak k i p (cl G v)).val x.2) (L x.1 + t • basis x.2)= ∑ j∈ Finset.range (k+1), frac p i k j t • (scatterM p v i j x) := by
 let r:= mid_charge p x.2 x.1; let u:=p i * (t-(1/2:ℝ)); unfold Tensor.diagonal; by_cases hh:x.2=i
 · rw [hh]; change (planeC i k _ _).val i _=_; rw [wearing]; simp_rw [prod_const, card_univ,Fintype.card_fin,center_point]; unfold scatterM; simp only [hh,ite_true]
   unfold frac; rw [add_pow]
   rw [Finset.sum_smul, Finset.smul_sum]; apply sum_congr rfl; intro j hj
   simp only [smul_smul]; congr 1; field_simp [(amt_p j).ne']
 simp_rw [speak, MS.Theater.away k _ e hh,_root_.zero_apply,scatterM,if_neg hh,smul_zero,Finset.sum_const_zero]
private def loss (p:QP)(i:Axis)(k j:ℕ) := ∫ t:ℝ in 0..1, frac p i k j t
private lemma round_point (p:QP)(i:Axis)(k:ℕ): loss p i k k=1:= by
 have he (t:ℝ) : frac p i k k t=1:= by unfold frac; rw [Nat.choose_self, Nat.cast_one,Nat.sub_self,pow_zero,mul_one,mul_one,div_self (amt_p k).ne']
 unfold loss; simp_rw [he]; simp
lemma projection_leg (k:ℕ) : integration G k (speak k i p (cl G v))= scatterM p v i k + ∑ j∈ Finset.range k, loss p i k j • scatterM p v i j:= by
    ext1 x; change (∫ t:ℝ in 0..1, Tensor.diagonal _ _) = _
    simp_rw [pinPoint p v i]; rw [intervalIntegral.integral_finsetSum ..]; simp_rw [intervalIntegral.integral_smul_const]; rw [Finset.sum_range_succ]; simp only [show (∫ (t:ℝ) in 0..1, frac p i k k t)=1 from round_point p i k,one_smul,Pi.add_apply, Finset.sum_apply,Pi.smul_apply]; rw [add_comm]; rfl
    intro j _; apply Continuous.intervalIntegrable; exact (show Continuous (frac p i k j) by unfold frac; fun_prop).smul continuous_const
variable (t:Labels.Key G)
local notation "h" => Sigma.fst t
local notation "w" => h+1
local notation "E'" => fderiv ℝ (box A t) 0
lemma unmid (k:ℕ)(hk:k≤w)(ht:h<d-1) : E' (coord A (integration G k (speak k i p (cl G v))))= if k=w then (pick t (yard G h (speak (h+1) i p (cl G v)))).re else 0:= by
 rw [box_der]; match k with
 | 0=> rw [constant,map_zero, if_neg (by omega)]
 | k+1=>
    rw [projection A _ (by omega)]; split
    next hi=>
            replace hi:k=t.1:= by omega
            subst k; change (Labels.coord (expand _ _) t).re= _; unfold Labels.coord; rw [snaps_eq]; rfl
    next hi=> change (Labels.coord (expand _ _) t).re= _; unfold Labels.coord; rw [snaps_off _ _ _ (show t.1 ≠ k by omega)]; simp
lemma mids (k:ℕ)(hk:k≤w)(ht:h<d-1) : E' (coord A (scatterM p v i k)) = if k=w then (pick t (yard G h (speak (h+1) i p (cl G v)))).re else 0:= by
    induction k using Nat.strong_induction_on with
    | _ u ih=>
       rw [← unmid A p v i t u hk ht, projection_leg]
       have he i' (hh:i'∈Finset.range u) := ih i' (Finset.mem_range.mp hh) ((Finset.mem_range.mp hh).le.trans hk); rw [map_add,map_add,map_sum,map_sum,Finset.sum_eq_zero,add_zero]; intro i' hI
       rw [map_smul,map_smul, he i' hI,if_neg (by have := Finset.mem_range.mp hI; omega),smul_zero]
end
end YM.FVA2.Press.Integration
