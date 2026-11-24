import YM.Qlocal.Versal.Vienna
import YM.Qlocal.Canopy.Lithe
/-!
 # Earnings in genuine regulator path letters
 Uniform any assignments, keep full paths & stage width before evaluating group fields.
 Qa pays entire function on actual pe.Poren.Coord.Frame; all h.Ar.Length.Tuple.Cη.
 This variant permits long-tail deletions in the **analytic estimator only**, after still requiring exact
 identities on old masks. See Tale.frugal for leftderivative *published labels* themselves
 (with root heat and power). These estimates instead go to full curvature derivatives
 used at AUX.Model window. KEEP COMPLEX GERM through Θ comparator!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open Function Filter Lattice Laurent RG Wilson Stationary Metric
open Marker Multi Finset
open Push Uniform
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
open ConnectedActivityE6.Blaze ConnectedActivityE6 AnalyticBridge Quipu Quipu.Sonnet
variable {V:Type}[DecidableEq V] {ι E:Type} {G:Gauge}{k n j r i z m w:ℕ} {c:Side} {d t a b v u C φ g:ℝ}{R:Census V}
namespace Cider
open Album Vase
variable {s:Senses R} (p : ℕ→ Prop)(A:Album ℕ s G n) (h: Health A (a+b) C)(he:∀ i,p i→ w ≤ (A i).momentum) (ha:0<a) (hb:0 ≤ b)
variable (o:Site c)(W:Config G c)
include he h ha hb
def nod (b:ℝ)(w:ℕ):= Real.exp (-b*w)
local notation "D"=> nod b w
lemma faith (i:ℕ)(hi:p i): (A i).fare a ≤ D*(A i).fare (a+b):= by
 unfold nod Vase.fare; rw [mul_left_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (nn_size _); linarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ) |>.mpr (he i hi)) hb]
lemma faithful (t':ℕ): ‖A.realize p o t' W‖≤ ticketC G t' n * D * C:= by
 let f i:= ‖A.readout p o t' i W‖; have ht: Summable f:=(A.global_sum p o W t' h (add_pos_of_pos_of_nonneg ha hb)).norm
 have he(i):f i ≤ ticketC G t' n*D* (A i).fare (a+b):= by
    by_cases hh:p i; · unfold f Album.readout; rw [if_pos hh,mul_assoc]; exact ((A i).paid o W ha _).trans (mul_le_mul_of_nonneg_left (faith p A h he ha hb i hh) (ticketC_pos ..)) -- h in args.
    unfold f Album.readout; rw [if_neg hh,Pi.zero_apply,norm_zero]; exact mul_nonneg (mul_nonneg (ticketC_pos ..) (Real.exp_nonneg _)) (h.1 i)
 apply (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum he (h.2.1.mul_left _)).trans ?_); rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (mul_nonneg (ticketC_pos ..) (Real.exp_nonneg _))
-- TRUE period orientation.Runtime coupled K.WARP.Fully analytic derivatives at all true fields.
variable [NormedAddCommGroup E][NormedSpace ℝ E]{y:E}{U:E→ Config G c}(hu:Mode U y k d) (hU : Weather U y) (t':ℕ)
local notation "q0"=> A.realize p o t'
local notation "f0"=>capita G n t' k d a
include hu hU
lemma upper: Allows k (q0 ∘ U) y (f0*D*C):= by
 have hx:= add_pos_of_pos_of_nonneg ha hb; obtain ⟨s₀,hs⟩:= Album.habitat U hU k;
 let z:= f0; let p' i:= A.readout p o t' i ∘ U; let M i:= f0*D*(A i).fare (a+b); have hg : 0≤z:= capita_ge G n t' k hu.pos ha; have hv:= h.2.1.mul_left (z*D);
 have hp'(i): Brush k (M i) 1 (p' i) y:= by
   unfold p' Album.readout; by_cases h':p i; · rw [if_pos h']; exact ((A i).palace o hu t' ha).climb (by unfold M; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (faith p A h he ha hb i h') hg) le_rfl
   rw [if_neg h']; refine (Brush.certified (c:=(0:ℝ)) zero_le_one).climb (?_) le_rfl; rw [norm_zero]; exact mul_nonneg (mul_nonneg hg (Real.exp_pos _).le) (h.1 i)
 refine ⟨Album.winter p A o t' h hx U hU,fun i hi=>?_⟩
 have hk:= printing p A o t' h hx U hU hs hi; rw [←hk.tsum_eq]; let f j:= ‖iteratedFDeriv ℝ i (p' j) y‖; have hb(j): f j≤M j:= Brush.offer.mp (hp' j)|>.inside _ hi; have hp: Summable f:=hv.of_nonneg_of_le (fun i=> norm_nonneg _) hb
 refine (norm_tsum_le_tsum_norm hp).trans ((hp.tsum_le_tsum hb hv).trans ?_); rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h.2.2 (mul_nonneg hg (Real.exp_pos _).le) -- actually normJ? check.
end Cider
end YM.Qlocal.Feud
