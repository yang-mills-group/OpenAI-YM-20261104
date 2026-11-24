import YM.X.Feyn.Port
/-!
Cut and charge maps along local stationary orbit. FO jet formulas.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set Lattice Wilson PertExtension PertExtension.Chart PertExtension.Orb
open Pert.Orb (Potential positiveLinks takeLink)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Series Series.Radial
variable {G : Gauge} {n : Side} (he:Even n.val)
local notation "E" => Potential G n
local notation "A" => Dir G n

def stem (v:E) (a:Cotree n): G.Color := G.plog (G.mat (branch v a))
@[simp] lemma stem_zero: stem (0:E)=0:= funext (fun x=> by rw [stem,branch_zero,G.mat_one,G.plog_one];rfl)
lemma stem_smooth: ContDiffAt ℝ ω (stem (G:=G) (n:=n)) 0:= by
   apply contDiffAt_pi.mpr; intro x; exact (show ContDiffAt ℝ ω G.plog (G.mat (branch (0:E) x)) from (by rw [branch_zero,G.mat_one]; exact G.plog_diff)).comp 0 ((branch_smooth x).contDiffAt)
lemma local_stem : ∀ᶠ v:E in 𝓝 0, representative (stem v)= links 1 (branch v):= by
    have he (x:Cotree n): Tendsto (fun v:E=> branch v x) (𝓝 0) (𝓝 1):= by
       suffices h : Continuous (fun v:E=> branch v x) by simpa [branch_zero] using (h.tendsto 0)
       rw [(G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuous_iff]; exact (branch_smooth ..).continuous
    filter_upwards [eventually_all.mpr fun i:Cotree n=> (he i).eventually G.plog_right] with v hv; unfold representative; rw [funext (show ∀ i:Cotree n,G.lieExp (stem v i)=_ from hv)]
section
include he
lemma stem_self : stem ∘ fits (G:=G) he =ᶠ[𝓝 0] id:= by
    have hh(i:Cotree n): ∀ᶠ v:A in 𝓝 0, G.plog (G.mat (G.lieExp (v i)))=v i:= (show Tendsto (fun v:A=>v i) (𝓝 0) (𝓝 0) from (continuous_apply i).tendsto _).eventually G.plog_left
    filter_upwards [eventually_all.mpr hh] with v hv; unfold comp; funext i; rw [stem,branch_inc]; exact hv i

lemma on_orbit {f: Config G n→ ℝ} (hv:GaugeInvariant f) : f ∘ positiveLinks =ᶠ[𝓝 0] (f ∘ representative) ∘ stem:= by
   filter_upwards [local_stem (G:=G) (n:=n)] with v hv'; simp only [comp_apply,hv', ← worth he,hv _ _]
end

def cut : E →L[ℝ] A:= fderiv ℝ stem 0
def kink (v:E): A:= (1/2:ℝ) • iteratedFDeriv ℝ 2 stem 0 (fun _=> v)
-- upgrade
include he in
lemma cut_self (v:A): cut (fits he v)=v:= by
   have h := (stem_self (G:=G) he).fderiv_eq (𝕜:=ℝ); let u:=fits he (G:=G) |>.toContinuousLinearMap
   rw [fderiv_id] at h; change cut (u v)=_
   have hz : HasFDerivAt (stem ∘ u) (cut.comp u) 0:= (show HasFDerivAt stem (cut (G:=G)) (u 0) from by rw [map_zero];exact (stem_smooth.differentiableAt (by simp)).hasFDerivAt).comp _ u.hasFDerivAt
   rw [show cut (u v)= (cut.comp u) v from rfl,← hz.fderiv]; exact DFunLike.congr_fun h v

-- general angle sequence jet. Need someJ/r factor. derive by radial iteration; mathlib Tensor
variable (v:Potential G n)
def ray (r:ℝ):= stem (r • v)
lemma ray_diff : ContDiffAt ℝ ω (ray v) 0:= (show ContDiffAt ℝ ω stem ((0:ℝ) • v) from by rw [zero_smul]; exact stem_smooth).comp (f:=fun r:ℝ=>r • v) _ (by fun_prop)
lemma ray_one : Jet.someJ (ray v) 1=cut v:= by
   rw [Gauss.jo_one]; suffices ht: HasDerivAt (ray v) (cut v) 0 from ht.deriv; unfold ray; exact (show HasFDerivAt stem (cut (G:=G)) ((0:ℝ) • v) from by rw [zero_smul]; exact (stem_smooth.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt _ (by simpa only [one_smul] using ((hasDerivAt_id' (0:ℝ)).smul_const v))
lemma ray_two : Jet.someJ (ray v) 2=kink v:= by
   unfold Jet.someJ kink ray; have hz : ContDiffAt ℝ 2 stem ((0:ℝ)•v):= by rw [zero_smul];exact stem_smooth.of_le le_top
   have he:= iteratedDeriv_vcomp_two (g:=stem) (f:=fun r:ℝ=>r • v) hz (show ContDiffAt ℝ 2 (fun r:ℝ=> r • v) 0 from contDiffAt_id.smul contDiffAt_const)
   have hv : deriv (fun r:ℝ=>r • v)=fun _=> v:= funext (fun r=> by simpa only [one_smul] using ((hasDerivAt_id' r).smul_const v).deriv)
   rw [show (fun r:ℝ=>stem (r • v))= _ from (rfl : (fun r:ℝ=> _)=stem ∘ (fun r:ℝ=> r • v)), he, hv]
   rw [show iteratedDeriv 2 (fun r:ℝ=>r • v) 0=0 from ?_,map_zero,add_zero,zero_smul]; congr 1
   · norm_num [Nat.factorial]
   · rw [show 2=1+1 from rfl, iteratedDeriv_succ,iteratedDeriv_one,hv]; simp
include he
lemma tick_stem {f : Config G n→ℝ}(h:GaugeInvariant f)(p : A→ℝ)(hp:ContDiffAt ℝ ω p 0)(hw:p= f ∘ representative){j:ℕ}(hh:∀ i<j, jet p i=0) (i:ℕ)(hi : i≤j+1) : jet (f ∘ positiveLinks) i v = if i=j then jet p j (cut v) else if i=j+1 then jet p (j+1) (cut v) + fderiv ℝ (jet p j) (cut v) (kink v) else 0:= by
   have ha := on_orbit he h; rw [← hw] at ha
   have heq : jet (f ∘ positiveLinks) i v= Jet.someJ (p ∘ ray v) i:= calc
       _ = jet (p ∘ stem) i v:=by unfold jet; rw [(ha.iteratedFDeriv ℝ i).eq_of_nhds]
       _ = _:= homogeneous_derivative _ v i (((show ContDiffAt ℝ ω p (stem 0) from by rw [stem_zero];exact hp).comp 0 stem_smooth).of_le le_top)
   rw [heq, Gauss.tick_base hp (a:=ray v) (show Jet.Act (j+2) (ray v) (Jet.someJ (ray v)) from ⟨ray_diff v,fun _ _=>rfl⟩) (by simp [ray]) hh hi,ray_one,ray_two]
end YM.PositionX.Feyn
