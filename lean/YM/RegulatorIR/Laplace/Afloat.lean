import YM.RegulatorIR.Geometry.End
import YM.PertExtension.Interior

/-!
Finite-cutoff diagram bridge: parameter-dependent aspiration. Abstract finite
plane reader with total-dimensional NormTerms from PertExtension, not
inventing a density matching PT. Here at one fixed regulator, so constants
and powers of the Gaussian can all depend on the dimension. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Laplace
open PertExtension Series Series.Radial MeasureTheory Filter Function Set Metric
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical
variable {X Y:Type}
variable [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]

def LimitSphere (X:Type)[NormedAddCommGroup X]:= sphere (0:X) 1
variable {F: X × Y → ℝ}

-- Any pure-X positive homogeneous quadratic, trivially true if X dim 0.
def Trim (F:X × Y → ℝ) : Prop:= ∀ x:X,x≠0 → 0<jet F 2 (x,0)

def Gap (F:X × Y → ℝ) (D:ℝ): Prop:= ∃ c>0, ∃ g:ℝ,0≤g ∧ ∀ x y,‖y‖ ≤ D → c*‖x‖^2-g ≤ jet F 2 (x,y)

namespace Trim
variable (h:Trim F)
omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] in
lemma function_cont : Continuous (jet F 2) := by
 unfold jet; apply continuous_const.mul; exact Continuous.comp (iteratedFDeriv ℝ 2 F 0).coe_continuous (continuous_pi (fun _=>continuous_id))
include h
omit [FiniteDimensional ℝ Y] in
private lemma abuts (he:(sphere (0:X) 1).Nonempty): ∃ c>0,∃ d>0,∀ x∈ sphere (0:X) 1, ∀ y, ‖y‖≤ d→ c ≤ jet F 2 (x,y):=by
 have hX:=isCompact_sphere (0:X) 1
 let f x:= jet F 2 (x,0)
 obtain ⟨x,hx,hp⟩:=hX.exists_isMinOn he ((function_cont.comp (continuous_id.prodMk continuous_const)).continuousOn (f:=f)) -- syntax
 let c:=f x/2; have hc:0<f x:= h x fun hu=> by rw [hu] at hx; simp at hx
 have H:sphere (0:X) 1 ×ˢ ({0}:Set Y) ⊆ {p|c < jet F 2 p}:=by rintro ⟨z,y⟩ ⟨hg,rfl⟩; exact lt_of_lt_of_le (half_lt_self hc) (hp hg)
 obtain ⟨u,v,hu,hv,h1,h2,ht⟩:= generalized_tube_lemma hX isCompact_singleton (isOpen_lt continuous_const function_cont) H
 obtain ⟨d,hd,Hd⟩:= Metric.mem_nhds_iff.mp (hv.mem_nhds (h2 (mem_singleton (0:Y))))
 refine ⟨c,half_pos hc,d/2,half_pos hd,?_⟩
 intro z hz y hy; exact le_of_lt (show _ < jet F 2 (z,y) from ht ⟨h1 hz,Hd (mem_ball_zero_iff.mpr (by linarith))⟩)

-- can feed arbitrary compact bounds in each application
lemma usable {D:ℝ}(hp:0≤D): Gap F D:=by
 cases isEmpty_or_nonempty {x:X//x∈sphere (0:X) 1} with
 | inl hm=>
   -- X must be zero
   have hh (x:X):x=0:=by
     by_contra! hx
     have h' :‖x‖≠0:= (norm_pos_iff.mpr hx).ne'; exact hm.false ⟨‖x‖⁻¹ • x,by simp [norm_smul,h']⟩
   obtain ⟨y,hy,hv⟩:= (isCompact_closedBall (0:Y) D).exists_isMinOn ⟨0,mem_closedBall_self hp⟩ (show ContinuousOn (fun y=>jet F 2 (0,y)) _ from (function_cont.comp (continuous_const.prodMk continuous_id)).continuousOn)
   refine ⟨1,zero_lt_one, |jet F 2 (0,y)|, abs_nonneg _,fun x z hx=>?_⟩
   rw [hh x]; simpa using (show -|jet F 2 (0,y)|≤jet F 2 (0,z) from (neg_abs_le ..).trans (hv (mem_closedBall_zero_iff.mpr hx)))
 | inr hm=>
   obtain ⟨c,hc,d,hd,h'⟩:= h.abuts (by simpa [← Set.nonempty_coe_sort] using hm)
   let r:=D/d; let S : Set (X × Y):= closedBall 0 r ×ˢ closedBall 0 D; have hr: 0≤r:= div_nonneg hp hd.le
   obtain ⟨m,hm,H⟩:= ((isCompact_closedBall (0:X) r).prod (isCompact_closedBall (0:Y) D)).exists_isMinOn (show S.Nonempty from ⟨(0,0),mem_closedBall_self hr, mem_closedBall_self hp⟩) (show ContinuousOn (jet F 2) S from function_cont.continuousOn)
   let C:=c*r^2+ |jet F 2 m|
   have hv:0≤C:=by dsimp [C]; positivity
   refine ⟨c,hc,C,hv,?_⟩
   intro x y hx; rcases le_or_gt ‖x‖ r with hg|hg
   · have hh: c*‖x‖^2 ≤ c*r^2:=by gcongr
     exact le_trans (show c* ‖x‖^2-C≤jet F 2 m by dsimp [C]; linarith [neg_abs_le (jet F 2 m)]) (H ⟨mem_closedBall_zero_iff.mpr hg,mem_closedBall_zero_iff.mpr hx⟩)
   have hr':0<‖x‖:=hr.trans_lt hg
   let k:=‖x‖⁻¹; have hk:=inv_pos.mpr hr'
   have hb:c ≤ jet F 2 (k • x,k • y):=by
     apply h' (k • x) (by dsimp only [k]; simp [norm_smul,hr'.ne'])
     rw [norm_smul, Real.norm_of_nonneg hk.le]; exact inv_mul_le_iff₀ hr'|>.mpr (by have := (div_lt_iff₀ hd).mp hg; nlinarith)
   have ht: jet F 2 (x,y)= ‖x‖^2*jet F 2 (k • x,k • y):= (by rw [← jet_smul]; apply congr_arg; ext1 <;> simp [k, smul_smul,hr'.ne'])
   rw [ht];exact le_trans (sub_le_self _ hv) ((mul_comm c _).le.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg _)))
end Trim
end YM.RegulatorIR.Laplace
