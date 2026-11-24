import YM.Pier.Scene.Layout
import YM.RG17.Corners
/-! All-small-length compatibility of the station approach to the scene estimate.

Any finite bounded separated shape class, any finite demand of extra polynomial
depth, on actual sites. Explicit cell placements (right-closed convention) per
period. Step after Leader may depend on demand and r. Keep polynomial zoom of
all pricing, including comparison to reporting scale, with usual threshold
caveats. NO claim of approximate *field evaluation* when rounding from continuum
values! That would need more, e.g. derivative estimates. Here price those native
stencils in this band exactly. They can approximate each point to unusually good
relative geometric accuracy. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17.Panoramic
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open OPE OPE.Yarn Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Patrol PertExtension Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G)
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "C"=> R.family
local notation "A"=> R.family.path.levels
local notation "a"=> R.family.S.a
local notation "S!"=> R.family.S
set_option quotPrecheck false
variable {T0:Campaign R}{W:Campaign.Pillars R T0} {h:G.Simple}(U:Pier.Starter R h T0 W)

structure EnvelopeRange (m k t s : ℕ) (r:ℝ) : Prop where
   small : m < k
   zoom : a m/a k ≤ (H k)^(s+27)
   compat : H k ≤ 2*H m
   space : H m^(s+25) ≤ r/a k
   far : r/a k ≤ H k^(s+29)
   lots : 1 ≤ r/(t:ℝ)/(4*a k)
   extra : (R.family.path.levels.budget k).B^8 ≤ Nat.floor (r/(t:ℝ)/(4*a k))
   radius : r*4*t < 1/2

private lemma radius_below (z:ℕ) :
    ((R.family.path.levels.budget z).B:ℝ) ≤ (H z)^2+1 := by
   have he:(0:ℝ) ≤ H z:= (zero_lt_one.trans ((A).fits.delayed _)).le
   apply le_trans (Nat.ceil_lt_add_one (sq_nonneg (Real.log (H z))) |>.le)
   exact add_le_add_left (pow_le_pow_left₀ (Real.log_nonneg ((A).fits.delayed z).le) (Real.log_le_self he) 2) _

include U
open Spec
variable {f:Extraction.Order}{S:Table R.family.book}{F:Spec.Final R.family f S} (L:Layout F)
   (hL: Located L) (hZ : Comparably R L.level)
include hL hZ
lemma planning (s t:ℕ) (ht:0<t) : ∀ᶠ r in home, EnvelopeRange R (L.level r) (berth R (s+25) (L.level r)) t s r := by
   let q:= L.level; let V:= berth R (s+25); let p(z:ℕ):= H z
   let w:ℝ:=t; have hw: (1:ℝ)≤w:= by unfold w; exact_mod_cast ht
   have hp:0<w:= zero_lt_one.trans_le hw
   have hQ:= hL.level.growing
   have hx:= (Station.hat_rate (A) h).comp hQ
   have hM:∀ᶠ r in home,r < 1/(8*w):= nhdsWithin_le_nhds (gt_mem_nhds (show 0<1/(8*w) by positivity))
   filter_upwards [hZ,hQ.eventually (cruise R U (s+25)),positiveLength,hM,hx.eventually_ge_atTop (4*w),hx.eventually_ge_atTop 8] with r hr ⟨hc,hk⟩ ht hg hw' hj
   let z:= L.level r; let k:= V z
   have hT:4*w ≤ p z:= hw'; have hv:(8:ℝ) ≤ p z:= hj; have h0:1 ≤ p z:= ((A).fits.delayed _|>.le); have h1:0<p z:= zero_lt_one.trans_le h0
   have he: z < k:= (arrival R (s+25) z).1
   have ha : p z ≤ p k:= WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos h).le he.le
   have hc:p k ≤ 2*p z:= hc
   have hf(i): 0<a i:= (C).S.a_pos _
   have hd:a z/a k≤ p z^(s+27):= by
       apply (div_le_iff₀ (hf k)).mpr
       have hw:a z/p z^(s+27) ≤ a k:= by rw [div_eq_mul_inv, ← inv_pow]; exact hk
       exact ((div_le_iff₀ (pow_pos h1 _)).mp hw).trans_eq (mul_comm ..)
   have hh:p z^(s+25) ≤ r/a k:= (le_div_iff₀ (hf k)).mpr ((mul_comm _ _).trans_le ((arrival R (s+25) z).2.trans hr.1))
   let b:= r/w/(4*a k); let B:=((A).budget k).B
   have hpay: (B:ℝ)≤ p z^3:=by
       apply (radius_below R k).trans
       have hy:=add_le_add_left (pow_le_pow_left₀ (ha.trans' h1.le) hc 2) (1:ℝ)
       exact hy.trans (by nlinarith only [hv,mul_le_mul_of_nonneg_right hv (sq_nonneg (p z))])
   have hcook: (B:ℝ)^8 ≤ b:=by
       have hf:((B:ℝ)^8)*(4*w) ≤ p z^(s+25):=by
          refine ((mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hpay 8) hT (by positivity) (by positivity)).trans ?_)
          rw [← pow_mul,pow_mul]
          exact le_trans (le_of_eq (show (p z^3)^8*p z = p z^25 from by ring)) (pow_le_pow_right₀ h0 (Nat.le_add_left _ _))
       refine (le_div_iff₀ (mul_pos (by norm_num) (show 0<a k from (C).S.a_pos _))).mpr ((le_div_iff₀ hp).mpr ?_)
       have hx := ((le_div_iff₀ ((C).S.a_pos k)).mp (hf.trans hh)); exact le_trans (le_of_eq (by ring)) hx
   refine ⟨he,hd.trans (pow_le_pow_left₀ h1.le ha _),hc,hh,?_,?_,?_,?_⟩
   · change r/a k ≤ p k^(s+29)
     refine (le_trans (mul_le_mul_of_nonneg_right (show r ≤ a z*p z^2 from hr.2) (inv_pos.mpr (hf k)).le) ?_ : r*(a k)⁻¹ ≤ _ ) |>.trans' (le_of_eq (div_eq_mul_inv ..)) -- ensure type
     calc
       _ = (a z/a k)* p z^2:= by ring -- division normalize?
       _ ≤ (p z)^(s+27)*p z^2:= mul_le_mul_of_nonneg_right hd (pow_nonneg h1.le _)
       _ ≤ _:= by rw [← pow_add]; exact pow_le_pow_left₀ h1.le ha _
   · exact (one_le_pow₀ (mod_cast (R.family.path.levels.budget k).B_pos) (n:=8)).trans hcook -- arg
   · apply Nat.le_floor; push_cast; exact hcook
   have hx: r*(8*w) < 1 := (lt_div_iff₀ (by positivity)).mp hg; change r*4*w < _; linarith only [hx]
end YM.RG17.Panoramic
