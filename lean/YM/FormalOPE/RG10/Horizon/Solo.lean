import YM.FormalOPE.RG10.Horizon.Footing
import YM.FormalOPE.RG10.Horizon.Logs

/-! # Absolute position test profiles for far use

Includes adapters from the chosen real opposite-time matrix test to these absolute bump-region
geometry conventions. Scale factors are Jacobian factors on the *retained* marks, no restoring
an extra volume for the fused relative-reading slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Arrangements
open Position Grade Apertures Maxwell Labels MeasureTheory Topology Metric Function WithLp
open scoped Topology BigOperators ContDiff Classical
variable {m n : ℕ} (B : Rear n)
open Rear
-- one-vertex horizon buffer. carries product test but no convolution until shifting.
abbrev zeroAt : Fin (1+n) := Fin.castAdd n 0
private lemma smoothP : ContDiff ℝ ∞ (fun x:E4=> YM.points (fun _ : Fin 1=>x)):= slide_smooth
lemma own_compact (f:E4→ℝ)(h:HasCompactSupport f):HasCompactSupport (fun x:Points 1=>f (x 0)) := by
  let K:= (tsupport f); have H := (IsCompact.image (f:=slide (n:=1)) h (by exact smoothP.continuous))
  refine H.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun y hy=> ⟨y 0,subset_closure hy,by ext1 i; fin_cases i; rfl⟩) H.isClosed)
def sheet (x : Points (1+n)):= B.center (x (@zeroAt n))* B.ext ((@align 1 n).symm x).2
@[simp] lemma sheet_apply (x:Points 1) (y:Points n) : sheet B (align (x,y))= B.center (x 0)* B.ext y:=by rw [sheet, zeroAt,align_left,ContinuousLinearEquiv.symm_apply_apply]
lemma sheet_smooth : ContDiff ℝ ∞ (sheet B):=
    ContDiff.mul (B.narrow.comp (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _:Fin (1+n)=>E4) zeroAt).contDiff) (B.ext.contDiff.comp (contDiff_snd.comp ((@align 1 n).symm).contDiff))
lemma extra : tsupport (sheet B) ⊆ (@align 1 n) '' (tsupport (fun x:Points 1=>B.center (x 0)) ×ˢ (tsupport B.ext)):=by
  apply closure_minimal _ (IsCompact.image (own_compact B.center B.compact |>.prod B.ext.hasCompactSupport) align.continuous|>.isClosed)
  intro x hx; obtain ⟨⟨x,y⟩,rfl⟩:= (@align 1 n).surjective x
  change sheet B (align (x,y))≠0 at hx; rw [sheet_apply] at hx
  exact ⟨(x,y),⟨subset_closure (left_ne_zero_of_mul hx),subset_closure (right_ne_zero_of_mul hx)⟩,rfl⟩
lemma safe_sheet : tsupport (sheet B) ⊆ conf _:=by
  intro x hx; obtain ⟨⟨x,y⟩,⟨hp,hr⟩,rfl⟩:= extra B hx
  refine align_conf (fun i j _=> Subsingleton.elim _ _) (B.ext.tsupport_subset hr) ?_
  intro i j; fin_cases i; have ht : x 0∈tsupport B.center := by
     exact Set.MapsTo.closure (f:=fun x:Points 1=>x 0) (fun _ he=> he) (PiLp.continuous_apply 2 _ 0) hp
  exact dist_pos.mp (lt_of_lt_of_le B.amount (B.stable (x 0) ht _ hr j))

def soloTest : Test (1+n):=by
 have hK: HasCompactSupport (sheet B):=IsCompact.of_isClosed_subset (IsCompact.image (own_compact B.center B.compact |>.prod B.ext.hasCompactSupport) align.continuous) (isClosed_tsupport _) (extra B)
 have he : tsupport (fun x=>(↑(sheet B x):ℂ))=tsupport (sheet B):= by unfold tsupport; congr! 1; ext; simp
 exact ⟨fun x=>(↑(sheet B x):ℂ),Complex.ofRealCLM.contDiff.comp (sheet_smooth B), (by unfold HasCompactSupport; rw [he]; exact hK), he.symm ▸ safe_sheet B⟩ -- HasCompactSupport coerce problem
abbrev silver (t:ℝ): Test (1+n) := Next.UVStress.dilate (Real.exp_pos t) (soloTest B)
namespace Halo -- not Apertures.Halo so no dot
variable (b:Apertures.Halo)
def ribbon : Rear 1 where
  ext:= by
    let f (x:Points 1):= b.glare 1 (x 0); exact ⟨f,(b.glow 1).comp (PiLp.proj (𝕜:=ℝ) (p:=2) (β:=fun _:Fin 1=>E4) 0).contDiff,
      own_compact (b.glare 1) (HasCompactSupport.comp_homeomorph (b.bump.hasCompactSupport_normed (μ:=volume)) flip.toHomeomorph), fun _ _ i j _=> Subsingleton.elim _ _⟩
  center := b.soft
  narrow := b.glow 0
  compact:= b.bump.hasCompactSupport_normed
  gap := 4
  amount:= by norm_num
  stable := by
    intro z hz p hp i; let f(x:Points 1):= b.glare 1 (x 0)
    have he : p 0∈tsupport (b.glare 1):= by
      exact Set.MapsTo.closure (f:=fun x:Points 1=>x 0) (fun _ he=> he) (PiLp.continuous_apply 2 _ 0) (show p∈tsupport f from hp)
    have ht : dist (p 0) top≤1:=le_trans (b:=b.bump.rOut) (closure_minimal (fun x h=> ball_subset_closedBall (b.motion 1 x h)) isClosed_closedBall he) b.nice
    rw [show tsupport b.soft = _ from b.bump.tsupport_normed_eq] at hz
    have h : dist bottom z ≤1:=by rw [dist_comm]; exact (le_trans hz b.nice)
    fin_cases i; change 4 ≤ dist z (p 0); linarith only [dist_triangle bottom z (p 0),dist_triangle bottom (p 0) top,ht,h,(show 8 ≤ dist bottom top from distance_marks)]

lemma squared : soloTest (ribbon b)=b.shape:=by
 ext1 x
 obtain ⟨⟨x,y⟩,rfl⟩:= (@align 1 1).surjective x
 change (↑(sheet _ _):ℂ)=(↑(b.pane _):ℂ); rw [sheet_apply, b.pane_at, show (align (x,y)) 1=y 0 from align_right x y 0,show (align (x,y)) 0=x 0 from align_left x y 0]; rfl
end Halo
end YM.FormalOPE.RG10.Arrangements
