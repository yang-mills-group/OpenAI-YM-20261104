import YM.UVExt.MetricLimit
import YM.Next.STATIONARY.Level.Recurse
import YM.Work.F02.Series
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Filter Function Set Lattice Laurent Wilson Bloch Exterior Precision RG Bid NormedSpace
open scoped Classical Topology BigOperators ComplexConjugate ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (v : Dir G n)

local notation "𝒱" => G.Mat

def ray (d : Step) (x : Site n) (t : ℝ) := G.mat (d.read (represent (t • v)) x)

def curve (w : Walk) (x : Site n) (t : ℝ) := G.mat (travel (represent (t • v)) x w)

def linkRate := G.colorScale * ‖v‖

def signedDirection (d : Step) (x : Site n) : G.Color := if d.neg then -collect G v (d.used x) else collect G v (d.used x)
lemma ray_reveal (d x t) : ray v d x t = G.mat (G.lieExp (t • signedDirection v d x)) := by
  unfold ray Step.read represent increment signedDirection collect; split <;> simp only [Pi.smul_apply,Pi.one_apply,mul_one]
  · rw [smul_neg,Work.F03.exp_neg_color]
lemma ray_smooth (d x) : ContDiff ℝ ω (ray v d x) := by simp_rw [funext (ray_reveal v d x)]; exact G.exp_jet.comp (contDiff_id.smul contDiff_const)
lemma curve_cons (d w x) : curve v (d::w) x = ray v d x * curve v w (x+d.vec) := funext fun t=> G.mat_mul _ _
lemma curve_smooth (w x) : ContDiff ℝ ω (curve v w x) := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ih => rw [curve_cons]; exact (ray_smooth ..).mul <| ih _

lemma ray_deriv (b : G.Color) (k : ℕ) : iteratedDeriv k (fun t : ℝ=> G.mat (G.lieExp (t • b))) = fun t=> G.mat (G.lieExp (t • b)) * (G.colorMat b)^k := by
  let Z (t : ℝ) := G.mat (G.lieExp (t • b))
  have hZ : ∀ t : ℝ, HasDerivAt Z (Z t * G.colorMat b) t := by
    intro t; unfold Z; simp_rw [G.mat_lieExp,map_smul]; exact hasDerivAt_exp_smul_const ..
  induction k with
  | zero => simp
  | succ k ih =>
    change iteratedDeriv (k+1) Z=_
    rw [iteratedDeriv_succ,ih]
    funext t
    exact ((hZ t).mul_const _).deriv.trans (by rw [pow_succ',mul_assoc])

lemma ray_rate (d x t k) (X : 𝒱) :
    ‖iteratedDeriv k (ray v d x) t * X‖ ≤ linkRate v ^ k * ‖X‖ := by
  rw [show ray v d x =fun _ : ℝ=> _ from funext (ray_reveal v d x),ray_deriv, mul_assoc,Gauge.mul_frob_eq _ _ (G.mat_star_mul _)]
  have he : ‖G.colorMat (signedDirection v d x)‖ ≤ linkRate v := by
    unfold linkRate; rw [G.colorMat_norm]; exact mul_le_mul_of_nonneg_left (by
      unfold signedDirection collect; split
      · rw [norm_neg]; exact norm_le_pi_norm v _
      exact norm_le_pi_norm v _) G.colorScale_pos.le
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    exact (norm_mul_le ..).trans ((mul_le_mul he ih (norm_nonneg _) (by unfold linkRate; positivity [G.colorScale_pos])).trans_eq (by rw [pow_succ',mul_assoc]))

lemma curve_rate (w x t k) :
    ‖iteratedDeriv k (curve v w x) t‖ ≤ (w.length * linkRate v) ^ k * ‖(1:𝒱)‖ := by
  induction w generalizing k x t with
  | nil => change ‖iteratedDeriv k (fun _ =>(1:𝒱)) t‖ ≤ _; cases k <;> simp [iteratedDeriv_succ']
  | cons d w ih =>
    rw [curve_cons,iteratedDeriv_mul ((ray_smooth v ..).of_le (by simp)).contDiffAt ((curve_smooth v ..).of_le (by simp)).contDiffAt] -- v..
    let X := ray v d x; let p := x+d.vec; let Z := curve v w p
    calc
      _ ≤ ∑ i∈Finset.range (k+1), (linkRate v ^ i * (w.length * linkRate v)^(k-i)* (k.choose i:ℝ))* ‖(1:𝒱)‖ := (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi => ?_)
      _ = _ := (Finset.sum_mul ..).symm.trans (by rw [←add_pow,List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm])
    change ‖(k.choose i:𝒱) * iteratedDeriv i X t * iteratedDeriv _ Z t‖ ≤ _
    rw [mul_assoc,← nsmul_eq_mul]
    apply norm_nsmul_le.trans ((mul_le_mul_of_nonneg_left (ray_rate v _ _ _ _ _) (by positivity)).trans _)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih ..) (by unfold linkRate; exact by have := G.colorScale_pos; positivity)) (by positivity)).trans_eq (by ring)


def wordField : Links (Per n) (Multiplicative G.Color) := fun e => Multiplicative.ofAdd (collect G v e)
private lemma word_read (x : Site n) (a : Step) : Multiplicative.ofAdd (signedDirection v a x)=a.read (wordField v) x := by
  unfold signedDirection Step.read; cases a.neg <;> rfl
lemma link_travel (x w) : Multiplicative.ofAdd (linkSum (collect G v) x w)=travel (wordField v) x w := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => rw [linkSum,travel,←word_read,←ih]; rfl
private lemma link_unit (x a b) : linkSum (collect G v) x (oriented a b) = linkSum (collect G v) x [a,b]-linkSum (collect G v) x [b,a] := by
  apply Multiplicative.ofAdd.injective
  change Multiplicative.ofAdd _=Multiplicative.ofAdd (linkSum (collect G v) x [a,b]) * (Multiplicative.ofAdd (linkSum (collect G v) x [b,a]))⁻¹
  rw [link_travel,link_travel,link_travel, ← travel_reverse]
  rw [show stop x [b,a] = stop x [a,b] by simp only [stop]; abel, ← travel_append]
  rfl

lemma link_swap (x : Site n) (a b : Step) : ‖linkSum (collect G v) x [a,b] - linkSum (collect G v) x [b,a]‖ ≤ ‖dColor G n 1 v‖ := by
  rw [←link_unit, show ‖linkSum (collect G v) x (oriented a b)‖ = ‖linkSum (collect G v) (atFace x a b) (square a.dir b.dir)‖ from ?_]
  · cases a with | mk i ε => cases b with | mk j ε' =>
    rcases lt_trichotomy i j with hij|rfl|hji
    · let p : PlaqAxes := ⟨(i,j),hij⟩
      rw [show square (Step.mk i ε).dir (Step.mk j ε').dir=square p.val.1 p.val.2 from rfl, fundamental G]; exact norm_le_pi_norm ..
    · dsimp
      have he z : linkSum (collect G v) z (square i i)=0 := (link_unit _ z (posDir i) (posDir i)).trans (sub_self _)
      rw [he,norm_zero]; exact norm_nonneg _
    let p : PlaqAxes := ⟨(j,i),hji⟩
    rw [show ∀ z, linkSum (collect G v) z (square ..)=-linkSum (collect G v) z (square p.val.1 p.val.2) from fun z => by
       change linkSum (collect G v) _ (oriented ..) = -linkSum (collect G v) _ (oriented (posDir j) (posDir i)); rw [link_unit v ..,link_unit v ..,neg_sub], norm_neg, fundamental G]
    exact norm_le_pi_norm ..
  have h := price_shift_pos (M:=ℝ) (fun x : Multiplicative G.Color => ‖x.toAdd‖) (wordField v) (fun k => by exact norm_neg k.toAdd) (fun k g=> by simp) a b x
  simp_rw [← link_travel] at h; exact h

lemma link_append (a b l : Walk) {R : Type*} [AddCommGroup R] [One R] (x : Four R) (h : stop x a=stop x b) : ∀ u : Links R G.Color,
      linkSum u x (a++l)-linkSum u x (b++l)=linkSum u x a - linkSum u x b := by
  intro U
  have hp (a : Walk) (x : Four R) : linkSum U x (a++l)=linkSum U x a +linkSum U (stop x a) l := by
    induction a generalizing x with
    | nil => rw [stop,linkSum, List.nil_append,zero_add]
    | cons d t ih => simp only [List.cons_append,linkSum,stop,ih]; rw [add_assoc]
  rw [hp,hp,h]; abel

set_option maxHeartbeats 1400000 in
private lemma link_braid (x : Site n) (a : Step) (b c : Walk) : ‖linkSum (collect G v) x (a :: (b++c))-linkSum (collect G v) x (b++a::c)‖ ≤ b.length* ‖dColor G n 1 v‖ := by
  induction b generalizing x with
  | nil => simp
  | cons d b ih =>
    let u := collect G v
    let S := a::d::b++c
    let S' := d::b++a::c
    let T := d::a::b++c
    have hx : linkSum u x S - linkSum u x T = linkSum u x [a,d]-linkSum u x [d,a] := link_append [a,d] [d,a] (b++c) x (by simp only [stop]; abel) u
    have hy : linkSum u x T - linkSum u x S' = linkSum u (x+d.vec) (a::(b++c)) - linkSum u (x+d.vec) (b++a::c) := by
      unfold T S'
      conv_lhs => change linkSum u x (d::a::(b++c)) - linkSum u x (d::(b++a::c))
      simp only [linkSum,add_sub_add_left_eq_sub]
    calc
      _ = ‖linkSum u x S-linkSum u x S'‖ := rfl
      _ ≤ ‖linkSum u x S-linkSum u x T‖ + ‖linkSum u x T-linkSum u x S'‖ := calc
          _ = ‖linkSum u x S-linkSum u x T + (linkSum u x T-linkSum u x S')‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖linkSum u x S-linkSum u x T‖ + ‖linkSum u x T-linkSum u x S'‖ := norm_add_le ..
      _ ≤ ((d::b).length:ℝ)* ‖dColor G n 1 v‖ := by
        rw [hx,hy,List.length_cons, Nat.cast_add,Nat.cast_one,add_mul,one_mul]
        exact le_trans (add_le_add (link_swap v x a d) (ih (x+d.vec))) (add_comm _ _).le

private lemma rotate_stop {R : Type*} [AddCommGroup R] [One R] (a : Step) (b c : Walk) (x : Four R) : stop x (a::(b++c))=stop x (b++a::c) := by
  induction b generalizing x with
  | nil => rfl
  | cons d b ih =>
    rw [List.cons_append,List.cons_append]; simp_rw [stop]
    rw [add_right_comm x a.vec d.vec]; exact ih _

private lemma square_fee (N) {m l : ℕ} (h : m+(l+1)+1=N) : (m:ℝ)+((m+l:ℕ):ℝ)^2 ≤ (N:ℝ)^2 := by
  subst N
  push_cast
  nlinarith [Nat.cast_nonneg (α:=ℝ) m,Nat.cast_nonneg (α:=ℝ) l]

set_option maxHeartbeats 600000 in
lemma basket_bound (w : Walk) (x : Site n) : stop (0:Cover) w=0 → ‖linkSum (collect G v) x w‖ ≤ (w.length:ℝ)^2 * ‖dColor G n 1 v‖ := by
  induction h:w.length using Nat.strong_induction_on generalizing x w with
  | h N ih =>
    intro hv
    cases w with
    | nil => exact norm_zero.trans_le (by positivity)
    | cons a l =>
      have ha : a.rev∈l := by
        by_contra he
        have hf {d : Step} (hd : d ≠ a.rev) : 0 ≤ (d.vec:Cover) a.dir * (a.vec:Cover) a.dir := by
          rcases d with ⟨i,hi⟩; rcases a with ⟨j,hj⟩
          unfold Step.vec; by_cases hjk : j=i
          · subst j; cases hi <;> cases hj <;> simp_all [step,Step.rev]
          cases hi <;> cases hj <;> simp [step,Pi.single_eq_of_ne hjk]
        have hg (l : Walk) (ht : a.rev∉l) (x : Cover) : x a.dir *(a.vec:Cover) a.dir ≤ stop x l a.dir *(a.vec:Cover) a.dir := by
          induction l generalizing x with
          | nil => exact le_rfl
          | cons d l it => exact (le_trans (show _ ≤ ((x+d.vec):Cover) a.dir*(a.vec:Cover) _ by rw [Pi.add_apply,add_mul]; specialize hf (d:=d) (by rintro rfl; simp at ht); omega) (it (by simpa using List.not_mem_of_not_mem_cons ht) _))
        specialize hg l he (a.vec:Cover)
        rw [stop,zero_add] at hv
        rw [hv] at hg
        rcases a with ⟨i,h|h⟩ <;> simp [step,Step.vec] at hg
      obtain ⟨A,B,hA⟩ := List.mem_iff_append.mp ha
      let u := collect G v; let k := A++[a,a.rev]++B
      have hs {R : Type} [AddCommGroup R] [One R] (U : Links R G.Color) (x : Four R) : linkSum U x [a,a.rev]=0 := by
        rcases a with ⟨i,h|h⟩ <;> simp [linkSum,Step.rev,Step.used,Step.vec,sub_eq_add_neg]
      have hp {R : Type} [AddCommGroup R] [One R] (x : Four R) : stop x [a,a.rev]=x := by simp_rw [stop,Step.vec_rev,←sub_eq_add_neg,add_sub_cancel_right]
      have ht : linkSum u x k=linkSum u x (A++B) := by
        apply Multiplicative.ofAdd.injective
        rw [link_travel,link_travel]
        change travel _ _ ((A++_)++_)=travel _ _ (A++B)
        rw [travel_append,travel_append _ _ A,travel_append _ _ A,stop_append, show stop (stop _ _) [a,a.rev]=stop x A from hp (stop x A),←link_travel v (stop x A) [a,a.rev],hs (collect G v) (stop x A),show Multiplicative.ofAdd (0:G.Color) = 1 from rfl,mul_one (travel (wordField v) x A)]
      have hn : (A++B).length<N := by simp only [hA,List.length_cons,List.length_append] at h; rw [List.length_append]; omega
      have hz : stop (0:Cover) (A++B)=0 := by
        rw [hA,rotate_stop,List.append_cons A,List.append_cons _ a.rev, List.append_assoc A,stop_append,stop_append,show stop (stop (0:Cover) A) ([a] ++ [a.rev])=_ from hp _] at hv
        simpa [stop_append] using hv
      rw [hA]
      calc
        _ ≤ ‖linkSum u x (a::(A++a.rev::B))-linkSum u x k‖ + ‖linkSum u x k‖ := calc
            _ = ‖linkSum u x _ - linkSum u x k + linkSum u x k‖ := Eq.symm (congrArg norm (sub_add_cancel ..))
            _ ≤ ‖linkSum u x _ - linkSum u x k‖ + ‖linkSum u x k‖ := norm_add_le ..
        _ ≤ ((A.length:ℝ)+((A++B).length:ℝ)^2) * ‖dColor G n 1 v‖ := by
            rw [add_mul]
            apply add_le_add
            · unfold k; rw [List.append_assoc]; exact link_braid v x a A (a.rev::B)
            rw [ht]
            exact ih _ hn (A++B) x rfl hz
        _ ≤ (N:ℝ)^2 * ‖dColor G n 1 v‖ := by rw [List.length_append]; exact (mul_le_mul_of_nonneg_right (square_fee (m:=A.length) (l:=B.length) N (by simpa only [hA,List.length_append,List.length_cons] using h)) (norm_nonneg _))

end YM.UVExt.Paths
