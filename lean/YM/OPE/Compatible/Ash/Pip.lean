import YM.OPE.Compatible.Ash.Aroma
/-!
# Intracell H seam and ∞ far moment
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full Laurent
open scoped BigOperators Classical ContDiff
variable {n m:Side}
def twin (n:Side):Gloam where
   M i:=n*(2:Side)^i
   q:=2
   growth:=by decide
   law i:=by rw [pow_succ,←mul_assoc]; rfl
lemma image_pebbles (D:List Axis):∃ C≥0,∃ M:ℕ,∀ n:Side,M≤ n.val→∀ x:Cover,2*size x ≤ n.val→ ‖seam D n x‖≤C*dew n^(D.length+2):=by
   let k:=D.length+2; obtain ⟨C,hC,M,h⟩:=image_peck D; let r:ℝ:=(2:ℝ)⁻¹^k; have hr:r<1:=pow_lt_one₀ (n:=k) (by norm_num) (by norm_num) (by unfold k; omega); refine ⟨C/(1-r),by positivity,M,fun n hn x hx=>?_⟩; let U:=twin n; let f(i):=mildX D (wrap (U.M i) x)
   have hh:Even (2:Side).val:=⟨1,rfl⟩; have he:U.M 0=n:=by change n*2^0=n;simp
   have hw(i):(U.M i).val=n.val*(2:ℕ)^i:=by simp only [U,twin, PNat.mul_coe, PNat.pow_coe];rfl
   have H:Tendsto f atTop (𝓝 (hull D x)):=by
       apply calm _ _ U.sides; filter_upwards [eventually_ge_atTop 1] with i hi; rw [hw]; exact (Even.pow_of_ne_zero (show Even (2:ℕ) from hh) (by omega)).mul_left _
   have hz(i): dist (f i) (f (i+1))≤ C*dew n^k*r^i:=by
       have hg:n.val ≤ (U.M i).val:=by rw [hw]; exact Nat.le_mul_of_pos_right _ (by positivity)
       rw [dist_eq_norm]; apply (h _ (le_trans hn hg) _ (U.ratio i) (show _ from rfl) x (le_trans hx hg)).trans; apply le_of_eq; change C*dew _^k= _; unfold dew sizeR; rw [hw,Nat.cast_mul, Nat.cast_pow]; simp only [Nat.cast_ofNat,mul_inv,mul_pow,r,inv_pow]; rw [←pow_mul,←pow_mul,mul_comm i];ring
   unfold seam; rw [←dist_eq_norm]; conv_lhs => rw [←he]
   change dist (f 0) _ ≤ _; exact (dist_le_of_le_geometric_of_tendsto₀ r _ hr hz H).trans (le_of_eq (by ring))
end YM.OPE.Balsam
