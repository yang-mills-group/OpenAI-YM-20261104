import YM.Comparison.Density.Transport.Taylor
import YM.Next.FLUCTUATIONS.Charts

/-!
# Real group coordinates of actual arguments, with a uniform derivative price

Uniformity in the number of links must not come from a hidden equivalence of
changing norms. Here one-link compactness suffices (for each stipulated finite
derivative order); no global matrix exponential estimate with volume-dependent
constant. Constants in LinkTube are paid at the stated order: delay gates
involving growing order are separate, not inferred from existence here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Transport
open Function Lattice RG Wilson Filter WardBin.Lies AnalyticBridge.SectorAffine.Offset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

variable {G : Gauge} {n : Side}

def logField (U : Config G n) : Directions G n := fun e=> G.plog (G.mat (U e))

private def multiplyOrder : (l : ℕ) → (G.Mat × (Fin l → G.Color)) → G.Mat
  | 0,q=>q.1
  | j+1,q=> multiplyOrder j (G.mat (G.lieExp (q.2 0))*q.1,Fin.tail q.2)
private def readOrder (G : Gauge) (l : ℕ) := G.plog ∘ multiplyOrder l

private lemma multiply_zero (l : ℕ) (M : G.Mat) : multiplyOrder l (M,0)=M := by
  induction l generalizing M with
  | zero => rfl
  | succ l ih => change multiplyOrder l (G.mat (G.lieExp 0)*M,0)=M; rw [G.mat_lieExp_zero, G.mat_one,one_mul]; exact ih _

private lemma multiply_link (U : Config G n) (l : ℕ) (X : Slab G n l) (i : Edge (Site n)) :
    G.mat (chug l U X i)=multiplyOrder l (G.mat (U i),fun j=>X j i) := by
  induction l generalizing U with
  | zero=>rfl
  | succ l ih=> rw [chug, multiplyOrder,ih]; rfl

private lemma multiply_cont (G : Gauge) (l : ℕ) : ContDiff ℝ ω (multiplyOrder (G:=G) l) := by
  induction l with
  | zero=>exact contDiff_fst
  | succ l ih=> exact ih.comp ((ContDiff.prodMk
      ((G.exp_jet.comp (contDiff_pi.mp (contDiff_snd (n:=ω)) 0)).mul contDiff_fst)
      (contDiff_pi.mpr fun j=> contDiff_pi.mp contDiff_snd j.succ)))

/-- Costs chosen for the Gauge, then available at every volume. -/
structure LinkTube (G : Gauge) where
  radius : ℝ
  constant : ℝ
  grade : ℕ → ℝ
  strict : 0 < radius
  scale : 0 < constant
  tall (l) : 0 ≤ grade l
  log_size (u : G.El) : G.chord u < radius → ‖G.plog (G.mat u)‖ ≤ constant*G.chord u
  recovers (u : G.El) : G.chord u < radius → G.lieExp (G.plog (G.mat u))=u
  smooth (u : G.El) : G.chord u < radius → ContDiffAt ℝ ω G.plog (G.mat u)
  jets (u : G.El) (l : ℕ) : G.chord u < radius →
    Through l (readOrder G l) (G.mat u,0) (grade l)

theorem tube_exists (G : Gauge) : Nonempty (LinkTube G) := by
  obtain ⟨a,r,ha,hr,h⟩:= Next.Fluctuations.log_chart_cost G
  -- choose ball for ALL orders for the chart domain, derivative prices can grow
  obtain ⟨s,hs,hS⟩:= Metric.nhds_basis_closedBall.eventually_iff.1 (G.plog_diff.eventually (by simp))
  let t:=min r (s/G.colorScale)
  have ht: 0<t:=lt_min hr (div_pos hs G.colorScale_pos)
  let Y:= {u:G.El| G.chord u ≤ t}; have hY : IsCompact Y := (isClosed_le G.continuous_chord continuous_const|>.isCompact (X:=G.El))
  have hx u (hu:u∈Y): ContDiffAt ℝ ω G.plog (G.mat u):= hS (Metric.mem_closedBall.mpr (show dist (G.mat u) 1≤s from by
    rw [dist_eq_norm, ← Next.Fluctuations.chord_dist,mul_comm]; exact (le_div_iff₀ G.colorScale_pos).mp ((show G.chord u≤t from hu).trans (min_le_right ..))))
  have hp (j : ℕ): ∃ c:ℝ,0≤ c ∧ ∀ u∈Y, Through j (readOrder G j) (G.mat u,0) c:= by
    let F (u : G.El) := (G.mat u,(0: Fin j→ G.Color))
    obtain ⟨c,hc,H⟩:= Push.Uniform.exists_allows (f:=readOrder G j) (s:=F '' Y)
      ((show IsCompact Y from hY).image (G.continuous_mat.prodMk continuous_const)) (by
        rintro _ ⟨y,hy,rfl⟩; apply (show ContDiffAt ℝ ω G.plog (multiplyOrder j (F y)) from (multiply_zero j (G.mat y)).symm ▸ hx y hy).comp _ (multiply_cont G j).contDiffAt) j
    exact ⟨c,hc,fun i hi=> Through.control (H (F i) ⟨i,hi,rfl⟩)⟩
  choose c hc H using hp
  refine ⟨t,a,c,ht,ha,hc,fun u hh => (h _ (hh.le.trans (min_le_left ..))).2,fun u hh=> (h _ (hh.le.trans (min_le_left ..))).1,fun u hu=> hx u hu.le,fun u j hu=> H j u hu.le⟩

section Charts
variable (L : LinkTube G) (U : Config G n) (hU : ∀ i, G.chord (U i)<L.radius)
include hU

lemma recover_link : ∀ᶠ V : Config G n in 𝓝 U, increment 1 (logField V)=V := by
  have h i : ∀ᶠ V : Config G n in 𝓝 U, G.chord (V i)< L.radius := by
    let H : Config G n → ℝ := fun V=> G.chord (V i)
    apply (show Tendsto H (𝓝 U) (𝓝 (G.chord (U i))) from
      ((show Continuous H from G.continuous_chord.comp (continuous_apply i)).tendsto U)).eventually (gt_mem_nhds (hU i))
  filter_upwards [eventually_all.mpr h] with V hV
  funext i
  rw [increment,logField, L.recovers _ (hV i),Pi.one_apply,mul_one]

private lemma paid_link (i : Edge (Site n)) (l : ℕ) : Through l (fun A=> logField (chug l U A) i) 0 (L.grade l) := by
  let P : Slab G n l→L[ℝ] (G.Mat × (Fin l→ G.Color)) := ContinuousLinearMap.prod 0 (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj i ∘L ContinuousLinearMap.proj j)
  have hP := show _ from P.opNorm_le_bound (M := 1) zero_le_one fun X=> by
    change max ‖(0:G.Mat)‖ ‖(fun j:Fin l=> X j i)‖≤ _
    rw [norm_zero,one_mul]; exact max_le (norm_nonneg _) ((pi_norm_le_iff_of_nonneg (norm_nonneg X)).2 (fun j=> (norm_le_pi_norm ..).trans (norm_le_pi_norm ..)))
  let F := fun Y=> readOrder G l ((G.mat (U i),0)+Y)
  have hh:= L.jets (U i) l (hU i)
  have hf : Through l F (P 0) (L.grade l) := by
    rw [map_zero]; refine ⟨ContDiffAt.comp (𝕜:=ℝ) (g:=readOrder G l) (f:=fun y=> (G.mat (U i),(0:Fin l→ G.Color))+y) 0 ?_ (contDiffAt_const.add contDiffAt_id),fun j hj=>?_⟩
    · simpa using! hh.smooth
    rw [show iteratedFDeriv ℝ j F 0=iteratedFDeriv ℝ j (readOrder G l) (G.mat (U i),0) by unfold F; rw [iteratedFDeriv_comp_add_left,add_zero]]
    exact hh.pay j hj
  refine (show F ∘ P = fun X=> logField (chug l U X) i from ?_) ▸ through_pull P hP hf
  funext A; unfold logField P F readOrder; rw [multiply_link]; simp

lemma paid_log (l : ℕ) : Through l (logField ∘ chug l U) 0 (L.grade l) :=
  through_pi (L.tall _) fun i=> paid_link L U hU i l

omit hU in
lemma chug_cont (l : ℕ) : Continuous (chug l U) := by
  refine continuous_pi fun i=> (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.continuous_iff.mpr ?_
  let F (X : Slab G n l) := (G.mat (U i),fun j=> X j i)
  have he : Continuous F:= continuous_const.prodMk (continuous_pi fun j=> (continuous_apply i).comp (continuous_apply j))
  convert! (multiply_cont G l|>.continuous).comp he using 1
  funext X; exact multiply_link U l X i

variable {w : ℝ} (hw : 0<w) (hw' : w≤1) (hx : ‖logField U‖ ≤ w)

def normLog (U : Config G n) (l : ℕ) (w : ℝ) : Slab G n l → Directions G n := w⁻¹ • ((logField ∘ chug l U) ∘ dilation _ w)
omit hU in
@[simp] lemma normLog_zero (l : ℕ) (w : ℝ) : normLog U l w 0 = w⁻¹ • logField U := by rw [normLog,Pi.smul_apply,Function.comp_apply,map_zero,Function.comp_apply,chug_zero]

include hw hx hw'
lemma log_tilt (l : ℕ) : Through l (normLog U l w) 0 (1+L.grade l) := by
  let Q := (logField ∘ chug l U) ∘ dilation _ w
  have he:= paid_log L U hU l
  have hP : ContDiffAt ℝ l Q 0:= (show dilation (Slab G n l) w 0=0 from map_zero _).symm ▸ he.smooth |>.comp _ (dilation _ _).contDiff.contDiffAt
  refine ⟨hP.const_smul w⁻¹,fun j hj=>?_⟩
  by_cases hz:j=0
  · subst j; rw [norm_iteratedFDeriv_zero, normLog_zero,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hw|>.le)]
    exact (show w⁻¹* ‖logField U‖ ≤ 1 from (inv_mul_le_iff₀ hw).2 (by simpa using hx)).trans (le_add_of_nonneg_right (L.tall _))
  change ‖iteratedFDeriv ℝ j (w⁻¹ • Q) 0‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hP.of_le (Nat.cast_le.mpr hj)),norm_smul, Real.norm_of_nonneg (inv_pos.mpr hw|>.le)]
  refine le_trans ?_ (le_add_of_nonneg_left zero_le_one); apply (inv_mul_le_iff₀ hw).2
  have hh : ‖iteratedFDeriv ℝ j Q 0‖ ≤ L.grade l*w^j:= dil_cost hw.le _ _ (by rw [smul_zero]; exact (through_le he hj).smooth) (by simp only [smul_zero]; exact he.pay j hj)
  exact hh.trans ((mul_le_mul_of_nonneg_left (by simpa only [pow_one] using pow_le_pow_of_le_one hw.le hw' (show 1≤j by omega)) (L.tall l)).trans_eq (mul_comm ..))

end Charts
end YM.Comparison.Density.Transport
