import YM.FormalOPE.RG10.Position.Tracks
import YM.Euclid.RPPeak

/-!
# One specific pair of absolute-position test profiles for the horizon inversion

Use matching time reflection on centers, their full profile geometry (not a statement only on
box-separated points). Use on E4 with Euclidean and patch(Test). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Apertures
open Position Position.Grade Function Finset Maxwell Labels PertExtension Extraction Filter Extra.FD
open MeasureTheory Topology Metric Matrix
open scoped Topology BigOperators ContDiff Classical
-- time reflection exactly through reference used for Signed graph conventions.
def flip : E4≃ₗᵢ[ℝ]E4 := Ortho.motion (Signed.reflect timeAxis)
def bottom : E4 := (-4:ℝ) • basis timeAxis
abbrev top : E4 := flip bottom
lemma below : time bottom= -4:= by simp [time,bottom]
lemma throughTime (x:E4) : time (flip x)= -time x:=by simp [time,flip]
lemma highest : time top=4:=by rw [top,throughTime,below]; norm_num
lemma flip_flip (x:E4) : flip (flip x)=x := by ext i; by_cases h:i=timeAxis<;>simp [flip,h]
lemma time_isometry (x y : E4) : |time x-time y|≤ dist x y := by
 change ‖(x-y) timeAxis‖ ≤ dist x y; rw [dist_eq_norm]; exact PiLp.norm_apply_le ..

local notation "ι" => Fin 2
abbrev marks : ι→ E4:= ![bottom,top]
lemma distance_marks : 8 ≤ dist (marks 0) (marks 1):=by
  convert! time_isometry bottom top using 1; rw [below,highest]; norm_num
lemma unique_marks : Function.Injective marks:= by
  intro i j he; fin_cases i <;> fin_cases j 
  all_goals try rfl
  all_goals exfalso; have ht:= distance_marks; simp_all; linarith
-- reserve 4 (pair separation) through reflected bumps support
structure Halo where
  bump : ContDiffBump bottom
  nice : bump.rOut ≤ 1
namespace Halo
variable (B:Halo)
def soft (v :E4) := B.bump.normed volume v
def glare : ι → E4→ℝ := ![B.soft,B.soft ∘ flip]
def pane (p:Points 2) := ∏ i, B.glare i (p i)
lemma pane_at (p:Points 2) : B.pane p=B.soft (p 0)*B.soft (flip (p 1)):=by unfold pane; simp [Fin.prod_univ_succ,Halo.glare]
lemma sign (i:ι) (p:E4):0 ≤ B.glare i p:=by fin_cases i <;> exact ContDiffBump.nonneg_normed ..
lemma glow (i:ι): ContDiff ℝ ∞ (B.glare i):=by
 fin_cases i
 · exact ContDiffBump.contDiff_normed (μ:=volume) (f:=B.bump) -- args
 exact (ContDiffBump.contDiff_normed (μ:=volume) (f:=B.bump)).comp flip.toContinuousLinearEquiv.contDiff
lemma nonneg (p : Points 2): 0 ≤ B.pane p:= prod_nonneg fun _ _=> B.sign ..
lemma smooth : ContDiff ℝ ∞ B.pane:= by
  unfold pane; exact contDiff_prod (t:=univ) (f:=fun (i:ι)(p:Points 2)=>B.glare i (p i)) (fun i _=> (B.glow i).comp (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _:ι=>E4) i).contDiff)
lemma motion (i:ι) (p:E4) (h:B.glare i p≠0) : p∈ ball (marks i) B.bump.rOut:=by
 fin_cases i
 · change p∈ ball bottom _; rw [← ContDiffBump.support_normed_eq B.bump (μ:=volume)]; exact h
 have he : flip p∈ball bottom B.bump.rOut:= by rw [← ContDiffBump.support_normed_eq B.bump (μ:=volume)]; exact h
 rw [mem_ball,← flip.dist_map]; simpa [marks, flip_flip] using (mem_ball.mp he)
lemma normal (i:ι) : ∫ x,B.glare i x=1:= by
 fin_cases i
 · exact ContDiffBump.integral_normed B.bump
 exact flip.measurePreserving.integral_comp' (f:=flip.toMeasurableEquiv) B.soft |>.trans B.bump.integral_normed
lemma narrow : tsupport B.pane ⊆ ⋂ i:ι,{p:Points 2| dist (p i) (marks i) ≤ B.bump.rOut} := by
 apply closure_minimal
 · intro p hp; exact Set.mem_iInter.mpr (fun i=> (by exact le_of_lt (mem_ball.mp (B.motion i (p i) (Finset.prod_ne_zero_iff.mp hp i (mem_univ _))))))
 apply isClosed_iInter; intro i; exact isClosed_le ((PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _:ι=>E4) i).continuous.dist continuous_const) continuous_const
lemma far {p:Points 2}(hp:p∈tsupport B.pane):4<dist (p 0) (p 1) := by
 have h1 : dist (p 0) bottom ≤1:= (show _ from (Set.mem_iInter.mp (B.narrow hp) 0)).trans B.nice
 have h2 : dist (p 1) top ≤1:= (show _ from (Set.mem_iInter.mp (B.narrow hp) 1)).trans B.nice
 rw [dist_comm] at h1; linarith only [h1,h2,dist_triangle bottom (p 0) (p 1), dist_triangle bottom (p 1) top, (show 8 ≤ dist bottom top from distance_marks)]
lemma separated {p:Points 2} (hp:p∈tsupport B.pane):p∈conf _:= by
 have h:= B.far hp
 intro i j he; fin_cases i <;> fin_cases j <;> try rfl
 · change p 0=p 1 at he; rw [he,dist_self] at h; norm_num at h
 change p 1=p 0 at he; rw [he,dist_self] at h; norm_num at h
lemma compact : HasCompactSupport B.pane := by
  let f:=fun i:ι=> closedBall (marks i) (B.bump.rOut); have H:=(isCompact_univ_pi (fun (i:ι)=>show IsCompact (f i) from isCompact_closedBall ..)).image (PiLp.continuous_toLp 2 _)
  refine H.of_isClosed_subset (isClosed_tsupport _) (fun p hp=> ⟨WithLp.ofLp p, fun i _=> Set.mem_iInter.mp (B.narrow hp) i, rfl⟩)
lemma unital : ∫ x,B.pane x=1:= by
 let H:= (PiLp.continuousLinearEquiv 2 ℝ (fun _:ι=>E4)).toHomeomorph.toMeasurableEquiv
 calc
   _ = ∫ x:ι→E4, ∏ i,B.glare i (x i):= by
     exact (Points.volume_product 2).integral_comp' (f:=H) (fun u=>∏ i,B.glare i (u i))
   _ = _:= by rw [integral_fintype_prod_volume_eq_prod]; simp_rw [normal]; simp

def shape : Test 2:= by
 have h : tsupport (fun x:Points 2=>(↑(B.pane x):ℂ))=tsupport B.pane:=by unfold tsupport; congr! 1; ext; simp
 refine ⟨fun x=>(↑(B.pane x):ℂ),Complex.ofRealCLM.contDiff.comp B.smooth, ?_, h.symm ▸ (fun _ hp=>B.separated hp)⟩
 unfold HasCompactSupport; rw [h]; exact B.compact
end Halo
end YM.FormalOPE.RG10.Apertures
