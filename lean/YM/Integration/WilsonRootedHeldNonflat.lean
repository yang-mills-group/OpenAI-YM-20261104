import YM.Integration.WilsonRootedHeldAffineFiled
import YM.Push.CORRECTED_COLUMNS.Integrals
import YM.Next.RANK.Ray

/-! A single true compact coarse bond with nonzero curvature at the
original plaquette, in every positive healthy collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldNonflat
open Lattice Wilson RG Filter
open scoped Topology Classical
variable {G:Gauge}

def needle (n:Side)(u:G.El):Config G n:=fun e=>if e=((0:Site n),(0:Axis)) then u else 1

def selected (n:Side):Face (Per n):=(0,⟨((0:Axis),1),by decide⟩)

private lemma word (n:Side)(hn:2≤n.val)(u:G.El):faceValue (needle n u) (selected n)=u:=by
  have away:(step (1:Axis):Site n)≠0:=by
    intro h
    have hw:(1:Per n).val=1:=(ZMod.val_eq_one hn _).2 rfl
    have hk:=congr_fun h (1:Axis)
    simp only [step_apply,if_true,Pi.zero_apply] at hk
    rw [hk] at hw
    simp at hw
  rw [selected,Push.Corrected.Torus.square_identity]
  simp [needle,away]

private lemma collar (n:Side)(u:G.El)(f:Face (Per n)):
    G.chord (faceValue (needle n u) f)≤4*G.chord u:=by
  let V:=needle n u
  have each (e):G.chord (V e)≤G.chord u:=by
    by_cases h:e=((0:Site n),(0:Axis)) <;> simp [V,needle,h,G.chord_nonneg]
  obtain ⟨x,⟨⟨a,b⟩,hab⟩⟩:=f
  change G.chord (faceValue V _)≤_
  rw [Push.Corrected.Torus.square_identity]
  let v:=V (x,a)
  let w:=V (x+step a,b)
  let z:=V (x+step b,a)
  let s:=V (x,b)
  have h:=G.chord_triangle (v*w*z⁻¹) s⁻¹
  have i:=G.chord_triangle (v*w) z⁻¹
  simp only [G.chord_inv] at h i
  change G.chord (v*w*z⁻¹*s⁻¹)≤4*G.chord u
  linarith only [h,i,G.chord_triangle v w,show G.chord v≤G.chord u from each _,
    show G.chord w≤G.chord u from each _,show G.chord z≤G.chord u from each _,show G.chord s≤G.chord u from each _]

theorem original (simple:G.Simple)(n:Side)(hn:2≤n.val){θ:ℝ}(hp:0<θ):
    ∃u:G.El,G.curvature (faceValue (needle n u) (selected n))≠0 ∧ flags θ (needle n u)=∅:=by
  haveI:=simple.nontrivial_color
  obtain ⟨b,hb⟩:=exists_norm_eq G.Color (c:=1) zero_le_one
  obtain ⟨H⟩:=Next.Rank.Spindle.charts G
  obtain ⟨r,rp,inside⟩:=Metric.nhds_basis_closedBall.eventually_iff.1 G.plog_left
  let t:=min r (min (H.c/2) (min (1/(8*H.C)) (θ/8)))
  have tp:0<t:=lt_min rp (lt_min (half_pos H.radius) (lt_min (by have:=H.positive;positivity) (by positivity)))
  have tr:t≤r:=min_le_left ..;have tc:t≤H.c/2:=(min_le_right ..).trans (min_le_left ..)
  have tC:t≤1/(8*H.C):=(min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))
  have tθ:t≤θ/8:=(min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))
  let v:=t•b
  have normv:‖v‖=t:=by simp [v,norm_smul,Real.norm_of_nonneg tp.le,hb]
  let u:=G.lieExp v
  have read:G.plog (G.mat u)=v:=inside (by simpa [Metric.mem_closedBall,normv] using tr)
  have light:G.chord u≤2*t:=by simpa [u,normv] using H.light v (by rw [normv];linarith only [tc,H.radius])
  have chart:=H.bars u (by linarith only [tc,light])
  rw [read] at chart
  refine ⟨u,?_,Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
  · rw [word n hn]
    intro h
    rw [h,sub_zero,normv] at chart
    have cap: t*(8*H.C)≤1:=(le_div_iff₀ (by have:=H.positive;positivity)).mp tC
    have small:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G.chord_nonneg _) light 2) H.positive.le
    nlinarith only [mul_le_mul_of_nonneg_right cap tp.le,chart,small,tp]
  · intro x h
    obtain ⟨f,-,bad⟩:=(flags_spec θ (needle n u) x).mp h
    linarith only [collar n u f,bad,light,tθ]

end YM.Integration.WilsonRootedHeldNonflat
