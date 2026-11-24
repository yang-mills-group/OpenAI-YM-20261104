import YM.Juniper.LocalAtlas.Agreement
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Awards
/-!
 # Caret = singleton quantitative wrap and germ calibration

 Need differentiability of FULL tsum of P.reg at genuine healthy chart at
 origin. Fixed volume ONLY internal to justifying existence ; don't spend this
 `scoped` bound after comparing jets. Narrow threshold using B existential
 retraction (values in nbhd) rather than pretending all native weighted
 directions fit in bought Poly chart on a wrapping torus.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Caret
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort Next.Foundations
open ConnectedActivityE6 Blaze Brush Fare Sienna Token Analysis Work.G05
open MultiNext.SignedSource.Lyre Measure Metric Set
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}
section summable
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {u C : ℝ}{j:ℕ} {f:ℕ → E → ℂ}{b:ℕ→ℝ}
local notation "S"=>Measure.sum (fun i:ℕ=> (1:ℝ≥0∞) • dirac i)
variable (he : ∀ᶠ x in 𝓝 0,∀ i:ℕ, Brush j (b i) 1 (f i) x) (hb : Summable b)
include hb he
lemma german : let F:= fun x=> ∑' i,f i x; ContDiffAt ℝ (↑j) F 0∧ ∀ i ≤ j, HasSum (fun r=> iteratedFDeriv ℝ i (f r) 0) (iteratedFDeriv ℝ i F 0):=by
   intro F
   let f':= fun i k=> f k i
   let q x i k:= iteratedFDeriv ℝ i (f k) x
   let T: Set E:= {x|∀ i,Brush j (b i) 1 (f i) x}
   have hT:T∈𝓝 0:=he; have h0:=mem_of_mem_nhds hT
   have hp x (hx:x∈T) i (hi:i≤j) (w): ‖q x i w‖≤ b w:= (Brush.offer.1 (hx w)).2 i hi
   have hm: Meristem f' 0 S j:= ⟨T,hT, ae_of_all _ (fun y x hx=> (hx y).smooth), fun i hi=> ⟨b,
     integrable_sum_dirac (fun _=> by norm_num) (show Summable (fun i:ℕ=> (1:ℝ≥0∞).toReal * ‖b i‖) from (by simpa only [Real.norm_eq_abs,ENNReal.toReal_one,one_mul] using! hb.abs)),fun x _=> ((continuous_of_discreteTopology : Continuous (JetF f' i x)).aestronglyMeasurable), ae_of_all _ (fun w x hx=> hp x hx i hi w)⟩⟩
   have hF:F=(fun x=>∫ i,f' x i ∂ S):=by ext1 x; rw [integral_sum_dirac (fun _=>by norm_num)]; simp only [ENNReal.toReal_one,one_smul]; rfl
   rw [hF]; refine ⟨hm.calls.1,fun i hi=>?_⟩; rw [(hm.calls.2 i hi).2]
   have H:Summable (fun t=> ‖q 0 i t‖):= Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (hp 0 h0 i hi) hb
   rw [integral_sum_dirac (fun _=> by norm_num)]; simp_rw [ENNReal.toReal_one,one_smul]; exact H.of_norm.hasSum
end summable

lemma flat_flags (n:Side)(t:ℝ)(ht:0<t): ∀ᶠ U: Config G n in 𝓝 1, flags t U=∅ := by
   have he (f:Face (Per n)): ∀ᶠ U: Config G n in 𝓝 1,G.chord (faceValue U f)<t:=by
      refine (show ContinuousAt (fun U:Config G n=> G.chord (faceValue U f)) 1 from (by unfold faceValue; fun_prop)).eventually (p:=fun y=>y < t) ?_
      apply gt_mem_nhds; change G.chord _ < _; unfold faceValue; simp [travel,square,ht]
   filter_upwards [eventually_all.mpr he] with U h; exact Finset.eq_empty_iff_forall_notMem.mpr (fun x hx=>by obtain ⟨l,-,ht⟩:= flags_spec .. |>.mp hx; exact ht.not_ge (h l|>.le))

section brush
open MultiNext.SignedSource.Lyre
variable (t : ℝ)(B:BudgetPoint) {n:Side}{K:Support n}{V:Config G n}
private def lowB (ht:0 < t)(hx:t≤B.threshold): BudgetPoint:= {B with threshold:=t,threshold_pos:=ht,threshold_le:= hx.trans B.threshold_le}
local notation "μ"=> MultiNext.SignedSource.Lyre.width
lemma narrow (n:Side)(o:Site n): ∃ (P:BudgetPoint), P.order=B.order∧ P.threshold ≤ B.threshold ∧ P.power=B.power∧ ∀ l: Edge (Site n),μ P o l ≤ 1:=by
  let a(x : Edge (Site n)):= (1+(separation x.1 o:ℝ))^B.power
  let t:=1+∑ l,a l; have ht: 0<t:= add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun l _=> by dsimp only [a]; positivity)
  let u:= min B.threshold t⁻¹; have he:0<u:= lt_min B.threshold_pos (inv_pos.mpr ht)
  refine ⟨lowB u B he (min_le_left ..),rfl,min_le_left ..,rfl,fun l=>?_⟩; change u*a l ≤ _; refine le_trans (mul_le_mul_of_nonneg_right (min_le_right ..) (by dsimp [a]; positivity)) ?_; rw [inv_mul_le_iff₀ ht,mul_one]; exact le_trans (Finset.single_le_sum (fun i _=> by dsimp only [a]; positivity) (Finset.mem_univ l)) (le_add_of_nonneg_left zero_le_one)
lemma narrowHealthy {u:ℝ} (h:u≤B.threshold) (he:Healthy u K V): Healthy B.threshold K V:= he.mono_right fun i hi=>by
   obtain ⟨x,hX,hv⟩:= (flags_spec ..).mp hi; exact (flags_spec ..).mpr ⟨x,hX,h.trans_lt hv⟩

variable {u:ℝ→ℝ}{k:ℕ} {Q : ℕ→Support n} {b : ℕ→ℝ} (f : ℕ→ Config G n→ℂ) (o:Site n) (hp : k ≤ B.order)
    (hd:∀ i,B.Regular (Q i) (f i)) (hv:∀ i,B.supBounds o (Q i) (f i) (b i))
local notation "Ds"=>Directions G n
local notation "L"=> increment (1:Config G n)
include hp hd hv
lemma complete : ∃ c:ℝ, ∀ᶠ x:Ds in 𝓝 0,∀ i:ℕ, Brush k (c*b i) 1 (f i ∘ L) x:=by
   obtain ⟨P,hP,hQ,hB,hC⟩:= narrow B n o; let θ:= P.threshold
   have ht := P.threshold_pos
   have hx(i): P.Regular (Q i) (f i):= by
     have he:= hd i; refine ⟨he.sites,he.borel,he.symmetry,fun y h=> by rw [hP]; exact he.smooth y (narrowHealthy B hQ h), fun y h u l hl=> he.hasDerivs y (narrowHealthy B hQ h) _ _ (hl.trans_le hP.le)⟩
   have hz (i): P.supBounds o (Q i) (f i) (b i) := by
     refine ⟨(hv i).1,fun U h l hl hL=> (hv i).2 U (narrowHealthy B hQ h) l (hl.trans hP.le) (fun A ha e=> (hL A ha e).trans ?_)⟩; rw [hB]; gcongr
   have ho : Continuous L := by unfold increment; fun_prop
   choose C hA H using fun j=> MultiNext.SignedSource.Lyre.general j 1 G
   let r(j:ℕ):=C j*θ⁻¹^j
   have hr:∀ j,0≤ r j:= fun j=> mul_nonneg (zero_le_one.trans (hA j)) (pow_nonneg (inv_pos.mpr ht).le _)
   refine ⟨∑ j∈Finset.range (k+1), r j,?_⟩
   have hf: Tendsto L (𝓝 0) (𝓝 1):= by simpa only [Work.G07.at_zero_increment] using (ho.tendsto 0)
   filter_upwards [hf.eventually (flat_flags n P.threshold ht), Metric.ball_mem_nhds _ (by norm_num : (0:ℝ)<1)] with x he h i
   have h': Healthy P.threshold (Q i) (L x):=by unfold Healthy; rw [he]; simp
   apply Brush.offer.2; refine ⟨(responsive 1 P (hx i) h').of_le (Nat.cast_le.mpr (hp.trans hP.ge)),fun j hj=>?_⟩; have hy:= (hv i).1
   apply le_trans (b:= r j*b i) ?_ (mul_le_mul_of_nonneg_right (Finset.single_le_sum (s:=Finset.range (k+1)) (fun l _=>hr l) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))) hy)
   apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (hr j) hy); intro m
   let v(l:Fin j):= ‖m l‖*θ⁻¹
   have hS(l):Sized (v l) (m l) P o:= by
     have hw(t): P.threshold≤μ P o t:= le_mul_of_one_le_right ht.le (one_le_pow₀ (by simp))
     refine ⟨mul_nonneg (norm_nonneg _) (inv_pos.mpr ht).le,fun e=>?_⟩; unfold v; rw [mul_assoc]; exact (norm_le_pi_norm (m l) e).trans (le_mul_of_one_le_right (norm_nonneg _) (by rw [inv_mul_eq_div,le_div_iff₀ ht, one_mul]; exact hw _))
   refine (H j n (Q i) P o x (f i) 1 (b i) m v (hj.trans (hp.trans hP.ge)) (hx i) h' (hz i) (fun e _=> ⟨(norm_le_pi_norm x e).trans (mem_ball_zero_iff.mp h).le, hC e⟩) hS).trans_eq ?_
   unfold v r; rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; ring
end brush

end YM.Juniper.Caret
