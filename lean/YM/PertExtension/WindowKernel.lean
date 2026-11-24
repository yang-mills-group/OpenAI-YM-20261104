import YM.PertExtension.AirCovariance
import YM.PertExtension.WilsonGrid

/-! Exact grid equality before passing to scaled jumps or taking real parts.
All target plaquette tests are on the Wilson quadratic form. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace YM.PertExtension.LatticePT.Projection
open MeasureTheory Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt
open Next.Rank.Beamer Air Band Orb Orbit GaussianScore Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {G : Gauge}{n:Side}

lemma scans_exact {F:E4→ℂ} (n:Side)(p:Site n→ℂ)(h:∀ t:Cover,F (addr n t)=hood (addr n t)*p (wrap n t)) :
   scansP n F 2=(nV n)⁻¹ * ∑ k:Site n,p k :=by
  unfold scansP
  rw [spray_sum n (fun t=>F (addr n t)) (by intro j hj;rw [h,hj,zero_mul])]
  simp_rw [h,spray_site,← Finset.sum_mul,hood_partition,one_mul]
  change (((n.val:ℝ)⁻¹)^4:ℝ) • _=_
  simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_eq_mul];unfold nV;push_cast;ring_nf

variable (a b:Degree G)(p y:FaceAt n)
def currentCross (k:Site n) :ℂ:= (if a.paint=b.paint then wedge (gradient k) (weight y k) p.2.val.1 p.2.val.2 else 0)
lemma denominator (k:Site n) (t:Cover) (h:wrap n t=k) :location (addr n t)= location (frequency k):= by subst k;unfold location;exact Finset.sum_congr rfl fun i _=>congr_arg (fun z:ℂ=>‖z‖^2) ((tone_step_wrap i t n).trans (tone_step ..))

lemma letterBand (ha:a.a=p.2)(hb:b.a=y.2)(t:Cover) :raw a b (addr n t)=currentCross a b p y (wrap n t):= by
   have he (i:Axis): gradient (wrap n t) i=increment i (addr n t):= (tone_step_wrap ..).symm
   have ht (i:Axis):backward (wrap n t) i= increment i (-(addr n t)):=tone_rev_wrap n i t
   unfold currentCross raw paints feather origin weight Air.brief Air.wedge
   simp only [ha,hb,zero_pow (by decide : 1≠0)];simp_rw [he,ht]; unfold pipe; split_ifs <;>(try tauto) <;> simp <;>ring
lemma disk_clean (k:Site n):
   (if a.paint=b.paint then disk (lighting y k) p else 0)= (nV n)⁻¹ * (tone (p.1-y.1) k * currentCross a b p y k / (location (frequency k):ℝ)) :=by
   have hx: tone (p.1-y.1) k=tone p.1 k * tone (-y.1) k:= by rw [sub_eq_add_neg,tone_add]
   rw [disk_aug]
   unfold wrinkle currentCross; simp_rw [show ∀ t, disk (perTone k t) p=tone p.1 k*wedge (gradient k) t p.2.val.1 p.2.val.2 from fun _=>disk_tone .., hx];split_ifs <;> ring

def licensed := if a.paint=b.paint then disk (shining y) p else 0
theorem plate_matches (z:Cover) (ha:a.a=p.2)(hb:b.a=y.2)(hz:wrap n z=p.1-y.1) : licensed a b p y=stepsP (shell a b) n 2 (mapZ z):=by
   let Q k:= tone (p.1-y.1) k*currentCross a b p y k/(location (frequency k):ℝ)
   let F (x):= wave (mapZ z) x* shell a b x
   change _=scansP n F 2
   have h (t:Cover):F (addr n t)=hood (addr n t)*Q (wrap n t):=by
      unfold F Q shell;rw [denominator _ t rfl,letterBand a b p y ha hb, ← phase_matches,hz];ring
   rw [scans_exact n Q h,Finset.mul_sum]
   unfold licensed
   let c(k:Site n):= if a.paint=b.paint then disk (lighting y k) p else 0
   have H : ∀ k:Site n, c k=(nV n)⁻¹ * Q k:=fun i=>disk_clean a b p y i
   rw [← Finset.sum_congr rfl (fun i (_:i∈Finset.univ)=>H i)]
   unfold c;by_cases h:a.paint=b.paint
   · simp only [if_pos h,disk_shining]
   simp only [if_neg h,Finset.sum_const_zero]

end YM.PertExtension.LatticePT.Projection
