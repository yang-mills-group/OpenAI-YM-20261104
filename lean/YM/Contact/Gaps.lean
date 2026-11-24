import YM.Contact.Jacobi
import YM.Contact.Power
import YM.Euclid.Lift

/-! Relative normal gap and local threshold. The tube and all integration measures remain
Euclidean; no identity of test-function contact jets with any other prescription is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts
open Set Function MeasureTheory Metric Filter LinearMap
open scoped Topology Pointwise BigOperators ContDiff
variable {G:Gauge}{L:Register G}{S T:Table L}
variable {k : ℕ}{F:Type*} [NormedAddCommGroup F]

def airborne (k:ℕ):Set (Points k) := differences k ⁻¹' conf (k+1)

def jacobiCLM:Points (k+1) →L[ℝ] Points k:=(ContinuousLinearMap.snd ℝ E4 (Points k)).comp (LinearMap.toContinuousLinearMap (coordinates k).toLinearMap)

def differencesCLM: Points k→L[ℝ] Points (k+1) := LinearMap.toContinuousLinearMap <| (Submodule.subtype _).comp (stair k).toLinearEquiv.toLinearMap

lemma airborne_open (k:ℕ) : IsOpen (airborne k) := conf_open _ |>.preimage (differencesCLM (k:=k)).continuous

lemma gen_valid (v){y:Points k} (hy:y∈airborne k):gen k v y∈conf (k+1):=by
  intro i j hi; exact hy (add_left_cancel (show v+_ = v+ _ from hi))
lemma relative_valid(x:Points (k+1)) (hx:x∈conf _):jacobi k x∈ airborne k:=by
  intro i j hi; exact hx (sub_eq_zero.mp ((centered_sub k x i j).trans (sub_eq_zero.mpr hi)))

private def value (x:Points k) (p : Option (Fin (k+1) × Fin (k+1))) := p.elim 1 fun q=> if q.1=q.2 then 1 else ‖differences k x q.1-differences k x q.2‖
/-- Capped Euclidean (normal Jacobi) gap (one on singleton clusters, zero on proper or total collision). -/
def gap (x:Points k) : ℝ:= Finset.inf' Finset.univ Finset.univ_nonempty (value x)
lemma gap_nonneg(x:Points k):0≤gap x:=by
  apply Finset.le_inf'; intro q _; cases q; exact zero_le_one; unfold value; dsimp; split_ifs; exact zero_le_one; exact norm_nonneg _
lemma gap_le_one(x:Points k):gap x≤1 := Finset.inf'_le (s:=Finset.univ) (value x) (b:=none) (Finset.mem_univ _)
lemma gap_le(x:Points k){i j:Fin (k+1)}(hi:i≠j):gap x ≤ ‖differences k x i-differences k x j‖:=
    (Finset.inf'_le (s:=Finset.univ) (value x) (b:=some (i,j)) (Finset.mem_univ ..)).trans_eq (if_neg hi)
lemma gap_le_add(x:Points k){i j:Fin (k+1)}(hi:i≠j):gap x ≤ 2*‖x‖:= (gap_le x hi).trans
    ((norm_sub_le ..).trans (by
        have he (t:Fin (k+1)): ‖differences _ x t‖ ≤ ‖x‖:= (PiLp.norm_apply_le ..).trans_eq (norm_diff ..)
        linarith only [he i, he j]))
lemma gap_pos (x : Points k) (hx:x∈airborne k):0<gap x:=by
  refine (Finset.lt_inf'_iff _).mpr fun q _=>?_
  cases q with
  | none=> exact zero_lt_one
  | some q=> unfold value; dsimp; split_ifs; exact zero_lt_one
             exact norm_pos_iff.mpr (sub_ne_zero.mpr ((hx:Injective _) |>.ne (by assumption)))
lemma zero_gap (hk : 1 ≤ k) :gap (k:=k) 0≤0:= by
   have _ : NeZero k:= ⟨Nat.ne_of_gt hk⟩
   exact (gap_le 0 (i:=(0:Fin k).succ) (j:=0) (Fin.succ_ne_zero _) |>.trans_eq (by rw [show differences k 0=0 from map_zero differencesCLM]; simp))
lemma live_gap (x:Points k)(hx:0<gap x):x∈airborne k:=fun _ _ hu=> Classical.byContradiction fun h=> (not_lt_of_ge (le_trans (gap_le x h) (by rw [hu,sub_self,norm_zero])) hx)

lemma gap_grows {x:Points k} (h:x∈airborne k){r:ℝ}(hr:0<r): min 1 r * gap x ≤ gap (r • x):=by
  refine Finset.le_inf' _ _ (fun q _=>?_)
  cases q with
  | none=> exact (mul_le_of_le_one_left (gap_pos _ h).le (min_le_left ..)).trans (gap_le_one _)
  | some p=> unfold value; dsimp; split_ifs with h'
             · exact (mul_le_of_le_one_left (gap_pos _ h).le (min_le_left ..)).trans (gap_le_one _)
             have he :differences k (r • x)=r • differences k x:= differencesCLM.map_smul ..
             simp only [he,PiLp.smul_apply,← smul_sub,norm_smul,Real.norm_of_nonneg hr.le]; exact mul_le_mul (min_le_right ..) (gap_le x h') (gap_pos x h|>.le) hr.le
lemma gap_hom {x:Points k}(_h:x∈airborne k) {r:ℝ}(hr:0<r)(hz:r*gap x≤1):r*gap x ≤gap (r • x):=by
  refine Finset.le_inf' _ _ (fun q _=>?_); cases q with
  | none=> exact hz
  | some p=> unfold value; dsimp; split_ifs with h'
             · exact hz
             have he :differences k (r • x)=r • differences k x:= differencesCLM.map_smul ..
             simp only [he,PiLp.smul_apply,← smul_sub,norm_smul,Real.norm_of_nonneg hr.le]; exact mul_le_mul_of_nonneg_left (gap_le x h') hr.le

lemma airborne_smul {x:Points k}(h:x∈airborne k){r:ℝ}(hr:0<r):r•x∈airborne k:=live_gap _ (lt_of_lt_of_le (mul_pos (lt_min zero_lt_one hr) (gap_pos _ h)) (gap_grows h hr))
lemma norm_le_cube (x y:E4): ‖x-y‖ ≤ 4*cubedist x y:=by
  let v:=x-y; have hh : ‖v‖^2 ≤ 4*cubedist x y^2:=by rw [PiLp.norm_sq_eq_of_L2]; refine le_trans (Finset.sum_le_card_nsmul _ _ (cubedist x y^2) fun i _=> ?_) ?_
                                                     · exact pow_le_pow_left₀ (norm_nonneg _) (show _ ≤ dist x.ofLp y.ofLp from by rw [dist_eq_norm]; apply norm_le_pi_norm) _
                                                     simp only [nsmul_eq_mul,Axis,Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat];rfl
  have he: 0 ≤ cubedist x y:= dist_nonneg; nlinarith

lemma pays_space (x:Points (k+1)):spaced (gap (jacobi k x)/4) x:=by
  intro i j h
  linarith only [show gap _ ≤ ‖x i-x j‖ from (centered_sub k x i j) ▸ gap_le _ h, norm_le_cube (x i) (x j)]

/-- Only a separated bound, *no* constraint at coincidences. -/
def Coarse (f : Points k → F) (m:ℕ) := ContinuousOn f (airborne _) ∧
    ∃ C:ℝ,0≤ C∧ ∀ x∈airborne _, ‖f x‖≤ C*(gap x)⁻¹^m


lemma capped_gap (H:T.Capped) (HS:T.Smooth)(w: Fin (k+1)→S.Tag):∃ m:ℕ, Coarse (fun y:Points k=>S.useAt T (differences k y) w) m :=by
  let t(i):= (w i).fst
  obtain ⟨m,C,hC,h⟩:= H _ t (fun i:Fin (k+1)=> S.representative _ (w i).snd) 0
  refine ⟨m,(S.class_smooth T HS w|>.continuousOn).comp differencesCLM.continuous.continuousOn (fun x hx=>hx),C*4^m,mul_nonneg hC (by positivity),fun x hx=>?_⟩
  have hv:jacobi k (differences k x)=x:=by simpa [gen] using jacobi_gen k 0 x
  specialize h _ (by positivity [gap_pos x hx]) (by linarith only [gap_le_one x]) (differences k x) (hv ▸ pays_space (differences k x))
  calc ‖S.useAt T (differences k x) w‖ ≤ C * (gap x/4)⁻¹^m := ?_
       _ = _ := by rw [inv_div,div_eq_mul_inv,mul_pow]; ring
  simpa only [norm_iteratedFDeriv_zero] using! h -- edit
end YM.Contacts
