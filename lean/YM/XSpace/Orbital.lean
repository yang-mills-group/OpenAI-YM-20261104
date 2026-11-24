import YM.XSpace.Concentration
/-!
# Preserve all color contractions => same color-orbit moments

Avoid assuming invariant polynomial relations completely presented: use
radially weighted averages and compact neighborhoods of a maximal Gram
fit. All actions in this calculation on true finite sets of colors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal MvPolynomial Metric OJoint
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff Classical
variable {D J:Type*}[Fintype D][Fintype J][DecidableEq J]
abbrev O (J : Type*)[Fintype J][DecidableEq J] := ↥(OJoint J)

-- Reynolds on the finite polynomial cylinder. Work with arbitrary linear reads,
-- no topological norm on MvPolynomial required.
private inductive Currency {V A:Type*} [TopologicalSpace A]: (A→poly V) →Prop
| coin (p:poly V)(f:A→ℂ)(h:Continuous f): Currency fun i=> f i • p
| sum {f g}: Currency f → Currency g→ Currency (f+g)
namespace Currency
variable {V A:Type*}[TopologicalSpace A]
private lemma factor {f g:A→poly V}(h:Currency f)(hs:Currency g): Currency (f*g):= by
  induction h with
  | sum _ _ hH hw=> rw [add_mul]; exact .sum hH hw
  | coin p f he =>
    induction hs with
    | sum _ _ h1 h2=> rw [mul_add]; exact .sum h1 h2
    | coin q g hs=>
      convert Currency.coin (p*q) (f*g) (he.mul hs) using 1; funext i; change (f i • p)*(g i • q)=(f i*g i) • (p*q); rw [smul_mul_assoc, mul_smul_comm,smul_smul]
private lemma pay_const (p:poly V): Currency (fun _:A=>p) := by simpa only [one_smul] using (Currency.coin p (fun _:A=>1) continuous_const)
private lemma lots {α:Type*}(S:Finset α)(f:α→A→poly V) (he:∀ i∈S,Currency (f i)): Currency (fun t=> ∑ x∈S,f x t):= by induction S using Finset.induction_on with|empty=>simp; exact pay_const ..| @insert i S hi ih=> simp_rw [Finset.sum_insert hi]; exact Currency.sum (he i (Finset.mem_insert_self ..)) (ih fun i hx=>he i (Finset.mem_insert_of_mem hx))
private lemma changes (p:Channel D J) : Currency (fun s:O J=>changing s p):= by
  induction p using MvPolynomial.induction_on with
  | C c=> simp only [changing,Normal.exchange_c]; exact pay_const _
  | add p q h t=> simp_rw [map_add]; exact Currency.sum h t
  | mul_X p i h=>
    simp_rw [map_mul]; refine factor h (g:=fun s:O J=> changing s (X i)) ?_
    simp only [changing,Normal.exchange_x, glyph,changeRow, _root_.map_sum,Finsupp.linearCombination_single]; refine lots _ _ (fun k _=> Currency.coin _ (fun s : O J=> (↑(s.val i.2 k):ℂ)) ?_); exact Complex.continuous_ofReal.comp ((continuous_apply k).comp ((continuous_apply i.2).comp continuous_subtype_val))

private lemma payout {A:Type*}[TopologicalSpace A][MeasurableSpace A][BorelSpace A][CompactSpace A] {μ:Measure A} [IsFiniteMeasure μ] {f:A→poly V} (h:Currency f): ∃ p:poly V,∀ L:poly V→ₗ[ℂ] ℂ,Continuous (fun i=> L (f i))∧ L p=∫ i:A,L (f i) ∂μ:= by
  induction h with
  | coin p f h=>
    refine ⟨(∫ x,f x ∂μ) • p,fun L=>?_⟩; simp_rw [_root_.map_smul,smul_eq_mul]; rw [integral_mul_const]; exact ⟨h.mul continuous_const,rfl⟩
  | sum _ _ h g=>
    obtain ⟨p,h⟩:= h; obtain ⟨q,v⟩:=g
    refine ⟨p+q,fun L=>?_⟩
    simp only [Pi.add_apply,map_add]; rw [(h L).2,(v L).2,integral_add ((h L).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((v L).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]; exact ⟨(h L).1.add (v L).1,rfl⟩
end Currency

def evoke (p:Channel D J) := (Currency.payout (μ:=OJoint.prob J) (Currency.changes p)).choose
lemma evoke_out (p:Channel D J) (L:Channel D J→ₗ[ℂ] ℂ):Continuous (fun s:O J=> L (changing s p)) ∧ L (evoke p)=∫ s:O J,L (changing s p) ∂(prob J):= (Currency.payout (μ:=prob J) (Currency.changes p)).choose_spec L
lemma evoke_gaze (p:Channel D J)(x:VectorA (D×J)) : watches (evoke p) x= ∫ s:O J,watches p (swept s x) ∂(prob J):= by simp_rw [← changing_value]; exact (evoke_out p (MvPolynomial.aeval (fun i=> (↑(x i):ℂ))).toLinearMap).2
lemma crossed_gaze (p:Channel D J)(x:VectorA (D×J))(s:O J): watches (evoke p) (swept s x)= watches (evoke p) x:= by rw [evoke_gaze, evoke_gaze]; simp_rw [← rotor_mul]; exact integral_mul_right_eq_self (fun s:O J=> watches p (swept s x)) _
lemma grid_full (P Q:Channel D J)(H:∀ x,watches P x=watches Q x): P=Q:= by
  refine MvPolynomial.funext_set (fun _=>Set.range Complex.ofReal) (fun _=>infinite_range_of_injective Complex.ofReal_injective) ?_; intro x hx
  choose p hp using fun i=> hx i (Set.mem_univ _); rw [← _root_.funext hp]; exact H (WithLp.toLp _ p)
lemma evoke_add (p q:Channel D J):evoke (p+q)=evoke p+evoke q:= by apply grid_full; intro x; let L:=(MvPolynomial.aeval (R:=ℂ) fun i=> (↑(x i):ℂ)).toLinearMap; change L _=L _; rw [_root_.map_add, (evoke_out (p+q) L).2,(evoke_out p L).2,(evoke_out q L).2];simp_rw [map_add]; exact integral_add ((evoke_out p L).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ((evoke_out q L).1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
lemma evoke_smul (p:Channel D J)(t:ℂ): evoke (t • p)=t • evoke p := by apply grid_full; intro x; let L:=(MvPolynomial.aeval (R:=ℂ) fun i=> (↑(x i):ℂ)).toLinearMap; change L _=L _; rw [_root_.map_smul,(evoke_out (t • p) L).2,(evoke_out p L).2];simp_rw [map_smul]; exact integral_smul _ _
def evokes (D J:Type*)[Fintype D][Fintype J][DecidableEq J]:Module.End ℂ (Channel D J):= ⟨⟨evoke,evoke_add⟩,fun c x=> evoke_smul x c⟩

lemma evoke_shadow {p:Channel D J}(h:Hide p): Hide (evoke p):= by
  intro l; let L:= (aeval (R:=ℂ) (0:D × J→ℂ)).toLinearMap.comp (tune l)
  change L _=_; rw [(evoke_out p L).2]; rw [show (fun i:O J=> L (changing i p))=fun _=>0 from _root_.funext fun i=> shade h i l]; exact integral_zero ..

private def gird (x:VectorA (D×J)) (a b:D):= inner ℝ (typed x a) (typed x b)
private lemma geo_reads (x:VectorA (D×J))(a b:D): watches (geo a b) x=(↑(gird x a b):ℂ):= by
  simp only [watches,geo,map_sum,map_mul,aeval_X,← Complex.ofReal_mul,← Complex.ofReal_sum]; unfold gird; rw [real_inner_comm]; rfl
private lemma gird_cont (a b:D): Continuous fun x:VectorA (D×J)=>gird x a b:= by unfold gird typed; fun_prop

lemma echo_gird (x:VectorA (D × J))(p:Channel D J)(y:VectorA (D×J))(h:gird x=gird y): watches (evoke p) x=watches (evoke p) y ∧ ‖x‖=‖y‖:= by
  obtain ⟨S,hs⟩:= OJoint.reconciles (typed x) (typed y) (fun i j=> congr_fun (congr_fun h _ ) _)
  constructor
  · rw [← crossed_gaze p x S, show swept S x=y from ?_]; apply PiLp.ext; intro i; exact congr_arg (fun z:VectorA J=> z i.2) (hs i.1)
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  have he :‖typed x i‖=‖typed y i‖ := by rw [← hs i,OJoint.spin_norm]
  change ∑ j,(typed x i j)^2= ∑ j,(typed y i j)^2
  rw [← EuclideanSpace.real_norm_sq_eq,← EuclideanSpace.real_norm_sq_eq,he]

lemma lost {p:Channel D J}(he: Hide p): evoke p=0:= by
  apply grid_full; intro x; let q:=evoke p; let t:= ‖x‖+1; let K:= Metric.closedBall (0:VectorA (D×J)) t
  have hP:watches q x=0:= by
    by_contra h
    let θ:= (watches q x)⁻¹; let f(y:VectorA (D×J)):= (bowl 0 t y • watches (θ • q) y).re
    let M (c:ℝ)(i j:D):= geo i j - C (σ:=D×J) (c:ℂ)
    let g(y:VectorA (D×J)):= ∑ i:D,∑ j:D, (gird y i j-gird x i j)^2
    let G :Channel D J:=∑ i:D,∑ j:D,M (gird x i j) i j^2 -- parse
    have hg: Continuous g:= continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> ((gird_cont i j).sub continuous_const).pow _
    have hG y : watches G y=(↑(g y):ℂ):= by
      unfold G g M watches; simp only [map_sum,map_sub,map_pow, Complex.ofReal_sum]; push_cast; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; simp only [show MvPolynomial.aeval _ _= (gird y i j:ℂ) from geo_reads y i j, aeval_C]; rfl
    have ht : IsCompact K:=isCompact_closedBall ..
    obtain ⟨A,hA⟩:= ht.bddAbove_image hg.continuousOn; let U:= max 1 A
    have hh : 0<U:= zero_lt_one.trans_le (le_max_left ..)
    let w y:= U-g y
    have hw : Continuous w:= continuous_const.sub hg
    have hx:x∈interior K:= interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball (show x∈Metric.ball (0:VectorA (D × J)) t from Metric.mem_ball.mpr (by simp [t]))
    have hw':w x=U:= by simp [w,g]
    have hc y (hy:y∈K):w y∈Set.Icc 0 U:= ⟨sub_nonneg.mpr ((hA (mem_image_of_mem g hy)).trans (le_max_right ..)),sub_le_self _ (Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=>sq_nonneg _)⟩
    have hm y (hy:y∈K)(hm:w y=U): 0<f y:= by
      have hs:g y=0:= sub_eq_self.mp hm
      have h' : gird y= gird x := by funext i j; have hh: (gird y i j-gird x i j)^2 ≤ 0:= le_trans (Finset.single_le_sum (fun j _=> sq_nonneg (gird y i j-gird x i j)) (Finset.mem_univ j)) ((Finset.single_le_sum (f:=fun i=> ∑ j,(gird y i j-gird x i j)^2) (fun i _=>Finset.sum_nonneg fun j _=>sq_nonneg _) (Finset.mem_univ i)).trans_eq hs); nlinarith
      obtain ⟨hv,hq⟩:= echo_gird y p x h'; unfold f;rw [show watches (θ • q) y= (1:ℂ) by change aeval _ (θ • q)=1; rw [map_smul]; change (watches q x)⁻¹*watches q y=_; rw [hv,inv_mul_cancel₀ h]] -- inspect
      simp [bowl,hq,t]; nlinarith [norm_nonneg x]
    have hf : Continuous f:= Complex.continuous_re.comp ((bowl_cont 0 t).smul (watch_kin (θ • q)).continuous)
    obtain ⟨n,hn⟩:= (concentrating volume K ht hf hw hh hc hm hx hw').exists
    let P:= MvPolynomial.C (σ:=D×J) (U:ℂ)-G
    have hP(n:ℕ): Hide (P^n*(θ • q)):= by
      induction n with
      | zero=> rw [pow_zero,one_mul]; exact (evoke_shadow he).scale _
      | succ n ih=>
        have ht (p:Channel D J)(h:Hide p)(i j:D):Hide (M (gird x i j) i j*p):= by unfold M; rw [sub_mul,C_mul']; exact (h.times i j).minus (h.scale _)
        have hy: Hide (G*(P^n*(θ • q))):= by unfold G; simp_rw [Finset.sum_mul, pow_two, mul_assoc (M _ _ _)]; refine Hide.testSum _ _ fun i _=> Hide.testSum _ _ fun j _=> ht _ (ht _ ih _ _) _ _
        rw [pow_succ',mul_assoc P,show ∀ Q :Channel D J, P*Q = C (U:ℂ)*Q-G*Q from fun z=> sub_mul .., C_mul']; exact (ih.scale _).minus hy
    have hV (y): watches (P^n*(θ • q)) y= w y^n • watches (θ • q) y:= by unfold P watches;rw [map_mul,map_pow,map_sub, show aeval _ _=(↑(g y):ℂ) from hG y,MvPolynomial.aeval_C, Complex.real_smul]; simp [w]
    have ht := latent _ (hP n) t 0
    change (∫ y,bowl 0 t y • watches (P^n*(θ • q)) y)=0 at ht
    have hu y : Complex.re (bowl 0 t y • watches (P^n*(θ • q)) y) = f y*w y^n:= by rw [hV, smul_comm,Complex.smul_re];exact mul_comm ..
    have hv := integral_re (pooling 0 t (watch_kin (P^n*(θ • q))).continuous)
    change (∫ y, Complex.re (bowl 0 t y • watches (P^n*(θ • q)) y))=_ at hv
    simp_rw [hu] at hv; rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) (by
      intro x hx; have hh : t<‖x‖ := lt_of_not_ge (fun he=>hx (Metric.mem_closedBall.mpr (by simpa using he)))
      rw [show f x=0 by unfold f bowl; rw [max_eq_right (show t^2-‖x‖^2≤0 from (by nlinarith [show 0<t from add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one])), zero_pow]; simp; omega,zero_mul])] at hv
    rw [ht] at hv; exact hn.ne' hv -- inspect
  exact hP.trans (map_zero _).symm
end YM.XSpace.Stab
