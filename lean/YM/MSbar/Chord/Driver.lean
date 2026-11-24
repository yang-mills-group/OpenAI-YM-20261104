import YM.MSbar.Chord.Echo
import YM.Work.E04
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free Finset
variable {G:Gauge}{n:Side}{σ:Type*} {Z B δ:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "N"=> (n.val:ℝ)
local notation "Θ"=>G.Color
noncomputable def size (n:Side):= (Fintype.card (Site n): ℝ)^2*n.val^2
lemma coord_price (x y:S₀)(i:Axis):|coord x y i| ≤ N :=by
    refine (small_coord ..).trans (Nat.cast_le.mpr ?_); unfold separation pdist; refine Finset.sup_le (fun i _=>?_ ); change (ZMod.valMinAbs _).natAbs ≤ n.val; rw [ZMod.valMinAbs_natAbs_eq_min]; omega -- inspect
variable (e:G.Color)
local notation "w!"=> tuner e
lemma hefty (X':X→X→ℝ)(he:∀ i j:S₀, |X' (w! i) (w! j)|≤ B):|gross X' e| ≤ B*size n:=by
    let d:=Fintype.card (Site n); unfold gross; apply (abs_sum_le_sum_abs ..).trans; refine (Finset.sum_le_sum (g:=fun _=>∑ i:S₀,B*N^2) (fun i _=>?_)).trans_eq ?_
    · apply (abs_sum_le_sum_abs ..).trans; refine Finset.sum_le_sum (fun j _=>?_); rw [abs_mul]; exact mul_le_mul (he i j) (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (coord_price ..) _) (abs_nonneg _) ((abs_nonneg _).trans (he i j))
    unfold size; simp only [sum_const,card_univ,nsmul_eq_mul]; ring
-- useful pass-to-tsum for each entry
lemma mosaic (F:σ→X→X→ℝ)(he:∀ i j : S₀, Summable (fun u=> F u (w! i) (w! j))) : Summable (fun u=> gross (F u) e)∧ gross (fun a b=>∑' u,F u a b) e= ∑' u,gross (F u) e:=by
    simp only [gross]; let g(i j:S₀)(k:σ):= F k (w! i) (w! j)*coord i j 0 ^2; have hp(i j):Summable (g i j):=(he i j).mul_right _; have hh(i:S₀) : Summable fun k:σ=>∑ j:S₀,g i j k:= summable_sum fun i _=> hp ..; exact ⟨summable_sum fun i _=>hh i,(by rw [Summable.tsum_finsetSum (fun i _=>hh i)]; apply Finset.sum_congr rfl; intro i _; rw [Summable.tsum_finsetSum (fun j _=> hp i j)]; exact sum_congr rfl fun j _=> (tsum_mul_right).symm)⟩
lemma pooling (F:σ→X→X→ℝ)(h:Finset σ): gross (fun a b=>∑ i ∈h,F i a b) e=∑ i∈h,gross (F i) e:=by
    unfold gross; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm (s:=h)]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm] -- unexpected first lhs
variable (x:Site n)(a b:Slot)(s: Signed) (F:G.Color→ₗ[ℝ]G.Color→ₗ[ℝ]ℝ)(p:ℕ)(hp:10*(p+4)<n.val)(he:‖e‖ ≤1)(hv: 0<δ)(hB:0≤B)(h: ∀ i j,|F i j|≤ B*‖i‖*‖j‖)
def year (F: G.Color →ₗ[ℝ] G.Color →ₗ[ℝ]ℝ)(x:Site n)(a b : Slot) := gross (fun z w=> F (curlX s (slotFace a x) z) (curlX s (slotFace b x) w)) e
local notation "u!"=> year e s F x -- params order inspect
noncomputable def url (n:Side)(p:ℕ)(δ:ℝ) := (16*size n+2)*Real.exp (-δ*p)
include hB hp he hv h
local notation "φ!"=> mark
lemma routeS (a b:Slot)(t:ℕ) (ha:a.length≤t)(hb:b.length≤t): |year e s F x a b - (-2* F (mark a.plaq e s) (mark b.plaq e s))| ≤ B* Real.exp (δ*t)*url n p δ:=by
    let M(i):=φ! i e s
    let A:=year e s F x a b; let D:=-2*F (M a.plaq) (M b.plaq)
    have hZ:0 ≤ 16*size n+2:=by unfold size; positivity
    by_cases ht:t ≤ p
    · change |A-D| ≤ _; rw [show A=D from ?_]; swap; · exact waveS s e F (slotFace a x) (slotFace b x) x p hp ((separation_comm ..).trans_le ((Work.E04.slot_separation a x).trans (ha.trans ht))) ((separation_comm ..).trans_le ((Work.E04.slot_separation b x).trans (hb.trans ht))) -- order
      unfold D url; rw [sub_self, abs_zero]; exact mul_nonneg (by positivity) (by positivity) -- M
    have hk(i:Face (Per n))(u:S₀) :‖curlX s i (w! u)‖ ≤4:=(readY s i e u).trans (by linarith only [he]); have hA:|A| ≤ B*4*4*size n:=by
        unfold A year; refine hefty e _ (fun i j=>?_); apply (h _ _).trans; exact mul_le_mul ((mul_le_mul_of_nonneg_left (hk _ _) hB)) (hk _ _) (norm_nonneg _) (by positivity)
    have hD:|D|≤2*B:=by unfold D; rw [abs_mul,abs_neg,abs_of_pos zero_lt_two]; apply mul_le_mul_of_nonneg_left _ (by norm_num); apply (h ..).trans; have hz(p): ‖mark p e s‖≤1:=(markN ..).trans he; exact (mul_le_of_le_one_right (mul_nonneg hB (norm_nonneg _)) (hz _)).trans (mul_le_of_le_one_right hB (hz _))
    have he:1 ≤ Real.exp (δ*t)*Real.exp (-δ*p):=by rw [← Real.exp_add]; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left (show (p:ℝ)≤ t from by exact_mod_cast (le_of_lt (lt_of_not_ge ht))) hv.le]
    change |A - D| ≤ _; refine (abs_sub ..).trans ((add_le_add hA hD).trans ?_); have hx:=le_mul_of_one_le_right (mul_nonneg hB hZ) he; unfold url; convert hx using 1 <;> ring
end YM.MSbar.Midpoint
