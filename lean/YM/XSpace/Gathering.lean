import YM.XSpace.Equality

/-!
# If all real moments agree then other configurations can be realized

Use across polynomial test orbits of stabilizer at a compact Gram radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Gather
open Function Set MeasureTheory MvPolynomial
open scoped BigOperators RealInnerProductSpace Classical
variable {A F: Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
variable (U W : A→F→ℝ)
private def y (U : A→F→ℝ) (x:F) : MvPolynomial A ℝ →ₐ[ℝ] ℝ:= aeval fun i => U i x
private abbrev w (r:ℝ): F→ℝ:= Snow.point r 0
def Match (r:ℝ):= ∀ n (i:Fin n→A),(∫ x,w r x*∏ a,U (i a) x) = ∫ x,w r x*∏ a,W (i a) x
variable {r :ℝ} (M : Match U W r) (hU :∀ i,Continuous (U i)) (hW:∀ i,Continuous (W i))
omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)] in
private lemma ycont (c : MvPolynomial A ℝ) (hU : ∀ i,Continuous (U i)): Continuous fun x=> y U x c:=by
  induction c using MvPolynomial.induction_on with
  | C c=>simpa only [y,aeval_C,Algebra.algebraMap_self,RingHom.id_apply] using (continuous_const (y:=c) (X:=F))
  | add p q hp hq=> simp only [map_add]; exact hp.add hq
  | mul_X p i hp=> simp only [map_mul, y,aeval_X]; exact hp.mul (hU i)
private def Things (U : A→F→ℝ) (r:ℝ) {n:ℕ} (T:Fin n→A) (c: MvPolynomial A ℝ) := fun x:F=>w r x*(y U x c * ∏ i,U (T i) x)
include M hU hW in
lemma combined (c:MvPolynomial A ℝ) : (∫ x,w r x*y U x c) = ∫ x,w r x*y W x c:=by
  suffices h: ∀ n (T:Fin n→A),(∫ x,Things U r T c x)= ∫ x,Things W r T c x by simpa [Things] using h 0 Fin.elim0
  have ht (n) (U:A→F→ℝ) (T:Fin n→A) (h:∀ i,Continuous (U i)) (p:MvPolynomial A ℝ): Integrable (Things U r T p):= Snow.finite r 0 (fun x:F=> y U x p * ∏ i,U (T i) x) ((ycont U p h).mul (continuous_finsetProd _ fun i _=> h _))
  induction c using MvPolynomial.induction_on with
  | C a=> intro n T; simp only [Things,y,aeval_C,Algebra.algebraMap_self,RingHom.id_apply,mul_left_comm (w r _) a,integral_const_mul,M n T]
  | add p q hp hq=>
    have he (U:A→F→ℝ) (n) (T:Fin n→A) : Things U r T (p+q)=Things U r T p+Things U r T q:=by funext; simp [Things,add_mul,mul_add]
    intro n T; simp_rw [he,Pi.add_apply]; rw [integral_add (ht n U T hU p) (ht n U T hU q), hp n T,hq n T, integral_add (ht n W T hW p) (ht n W T hW q)] -- possible point
  | mul_X p i hp=>
    intro n T; let I:= Fin.cons (α:=fun _=> A) i T; have he (U:A→F→ℝ): Things U r T (p*X i)= Things U r I p:= by
      funext x; simp only [Things,map_mul,y,aeval_X, Fin.prod_univ_succ, mul_assoc]; rfl -- rw nested FH
    rw [he U,he W]; exact hp (n+1) I

local notation "K" => Metric.closedBall (0:F) r
private lemma peak {p q : F→ℝ} (hp : Continuous p) (hq : Continuous q) {t:F} (hr : 0<r) (h : ‖t‖<r) (a:ℝ) (ha : 0<a) (hu:a<q t)
    (h1 : ∀ x∈K,0 ≤ p x ∧ p x≤a) (h2: ∀ x ∈ K,0 ≤ q x)
    (H : ∀ n:ℕ,(∫ x,w r x*p x^n) = ∫ x,w r x*q x^n) : False:=by
  let Z:= ∫ x:F,w r x
  have hin : Integrable (w (F:=F) r):=by simpa only [smul_eq_mul,mul_one] using Snow.finite r 0 (fun _ : F=> (1:ℝ)) continuous_const
  obtain ⟨b,hb,hb'⟩:=exists_between hu; have he : 0<b:=ha.trans hb
  let g (x:F):= w r x* min 1 (max 0 (q x-b)); let z:=∫ x:F,g x
  have hk : Continuous g:=(Snow.point_cont ..).mul (continuous_const.min (continuous_const.max (hq.sub continuous_const)))
  have hh (x:F): 0 ≤ g x:= mul_nonneg (Snow.point_nonneg ..) (le_min zero_le_one (le_max_left ..))
  have hi : Integrable g:=Snow.finite r 0 (fun x:F=>min 1 (max 0 (q x-b))) (continuous_const.min (continuous_const.max (hq.sub continuous_const)))
  have hz: 0<z:= integral_pos_of_integrable_nonneg_nonzero hk hi hh (show g t≠0 from (mul_pos (Snow.point_pos 0 hr h) (lt_min zero_lt_one (lt_max_of_lt_right (sub_pos.mpr hb')))).ne')
  have hout (x:F) (hx:x∉K) : w r x=0:= Snow.dead r 0 x (by rw [abs_of_pos hr]; apply le_of_lt; simpa [Metric.mem_closedBall] using hx)
  have up (n:ℕ): (∫ x,w r x*p x^n) ≤ Z*a^n:=by
    rw [← show (∫ x:F,w r x*a^n)=Z*a^n from integral_mul_const ..]; apply integral_mono (Snow.finite r 0 (fun x=> p x^n) (hp.pow _)) (hin.mul_const _)
    intro x; by_cases hx:x∈K; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h1 x hx).1 (h1 x hx).2 _) (Snow.point_nonneg ..)
    simp [hout x hx]
  have down (n:ℕ): z*b^n≤ (∫ x,w r x*q x^n):=by
    rw [← show (∫ x:F,g x*b^n)=z*b^n from integral_mul_const ..]; apply integral_mono (hi.mul_const _) (Snow.finite r 0 (fun x=> q x^n) (hq.pow _))
    intro x; by_cases hx:x∈K
    · rcases le_total b (q x) with h|h
      · exact mul_le_mul (show g x≤w r x by unfold g; exact mul_le_of_le_one_right (Snow.point_nonneg ..) (min_le_left ..)) (pow_le_pow_left₀ he.le h _) (pow_nonneg he.le _) (Snow.point_nonneg ..)
      change g x*b^n ≤ w r x*q x^n
      rw [show g x=0 by unfold g; rw [max_eq_left (sub_nonpos.mpr h),min_eq_right zero_le_one,mul_zero],zero_mul]; exact mul_nonneg (Snow.point_nonneg ..) (pow_nonneg (h2 x hx) _)
    simp [g,hout x hx]
  obtain ⟨n,hn⟩:=pow_unbounded_of_one_lt (Z/z) ((one_lt_div ha).mpr hb)
  rw [div_pow, div_lt_div_iff₀ hz (pow_pos ha n)] at hn; exact (not_lt_of_ge ((down n).trans ((H n) ▸ up n))) (by rwa [mul_comm z])

include M hU hW in
lemma realize_set (S : Finset A) (t:F) (hr : ‖t‖<r) : ∃ u∈K, ∀ i∈S,U i u=W i t:=by
  have hh (x:F): x∈ K ↔ ‖x‖≤r:=by simp [Metric.mem_closedBall];
  let V: MvPolynomial A ℝ:= ∑ i∈S, (X i - C (W i t)) ^ 2
  let p (x:F):= y U x V; let q (x:F):= y W x V
  let Q:= Metric.closedBall (0:F) r
  have hQ : IsCompact Q:= isCompact_closedBall ..
  have ht:t∈Q:= (hh _).2 hr.le; have he : Q.Nonempty:=⟨_,ht⟩
  have hk (U:A→ F→ℝ) (x:F): y U x V= ∑ i∈S,(U i x-W i t)^2:=by simp [V,y,map_sum]
  obtain ⟨z,hz,h⟩:=hQ.exists_isMinOn he (ycont U V hU).continuousOn; change ∀ x∈Q,_ at h --?
  have hp : 0≤p z:=by unfold p; rw [hk]; positivity
  by_cases hx : p z=0
  · refine ⟨z,hz,fun i hi=>?_⟩; apply sub_eq_zero.mp; exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun i _=> sq_nonneg (U i z-W i t))).mp ((hk U z).symm.trans hx) i hi)
  obtain ⟨x,hw⟩:= hQ.exists_bound_of_continuousOn (ycont U V hU).continuousOn
  obtain ⟨x',hw'⟩:= hQ.exists_bound_of_continuousOn (ycont W V hW).continuousOn
  let b:=max x x'+1
  let Y (g : F→ℝ) (x:F):= b-g x
  have he (u) (hu:u∈Q): p u<b:=lt_of_le_of_lt ((le_abs_self _).trans (hw u hu)) (by unfold b; linarith [le_max_left x x'])
  apply False.elim; refine peak (p:=Y p) (q:=Y q) (continuous_const.sub (ycont U V hU)) (continuous_const.sub (ycont W V hW)) (lt_of_le_of_lt (norm_nonneg _) hr) hr (b-p z) (sub_pos.mpr (he _ hz)) ?_ (fun i hi=>⟨(sub_pos.mpr (he _ hi)).le,sub_le_sub_left (h i hi) _⟩)
    (fun u hu=> sub_nonneg.mpr (le_trans ((le_abs_self _).trans (show |q u| ≤ x' from hw' u hu)) (by unfold b; linarith [le_max_right x x']))) ?_
  · have hh : q t=0:=by simp [q,hk]
    unfold Y; rw [hh]; exact sub_lt_sub_left (lt_of_le_of_ne hp (Ne.symm hx)) _
  intro n; have he x (U:A→F→ℝ): y U x ((C b-V)^n)=(b-y U x V)^n:=by simp [y]
  have hb := combined U W M hU hW ((C b-V)^n); simp_rw [he] at hb; exact hb
include M hU hW in
lemma realizes (t:F) (hr: ‖t‖<r):∃ u∈K,∀ i,U i u=W i t:=by
  let E (i:A):= {x:F|U i x=W i t}
  obtain ⟨u,h,h'⟩:= (isCompact_closedBall (0:F) r).inter_iInter_nonempty E (fun i=> isClosed_eq (hU i) continuous_const) (fun S=> by
    obtain ⟨z,hz,H⟩:= realize_set U W M hU hW S t hr; exact ⟨_,hz, mem_iInter.mpr fun i=>mem_iInter.mpr (H i)⟩)
  exact ⟨_,h, Set.mem_iInter.mp h'⟩
end YM.XSpace.Gather
