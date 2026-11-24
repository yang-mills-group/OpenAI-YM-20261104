import YM.RG01Estimate.InteriorAdmission
import YM.RG01Estimate.LaplaceTrunc
/-!
# Poly bills (one stage).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace
open Function Filter Set Metric Finset MeasureTheory
open Lattice Wilson Pressure RG Gauge Input Precision Tree Matrix
open PhysicalNext.Repeat Fare Lantern Sienna ConnectedActivityE6 Blaze Shield Brush RealTaylor Office Matrix
open Poll Push.AbsoluteSums Coat Lapis
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {G:Gauge} {L:Side}
local notation "B" => (fun z=> betaF G z L)
local notation "p" => Delay.fineMonitor G L
variable {f g : ℝ→ℝ}
structure Cookie (G:Gauge)(L:Side)(f:ℝ→ℝ): Prop where
  invoice : ∃ (C:ℝ) (k:ℕ), 0 ≤ C ∧ ∀ᶠ t in atTop,|f t|≤ C*(Delay.fineMonitor G L t)^k
namespace Cookie
lemma uses (h:Cookie G L f): Rate G L 0 f:= by
   obtain ⟨c,k,hc,H⟩:= h.invoice
   exact Rate.compare (show Rate G L 0 _ from by simpa only [zero_mul] using! (Rate.monitor (G:=G) (L:=L) |>.pow k).mul_left c) (H.mono fun _ h=> h.trans (le_abs_self _))
lemma bolt (h:Bolt G L f): Cookie G L f:= by
   refine ⟨1,1,zero_le_one,?_⟩
   simpa only [pow_one,one_mul,Real.rpow_one] using! h.listens (e:=1) zero_lt_one
lemma copy (h:Cookie G L f)(he:g =ᶠ[atTop] f): Cookie G L g:= by obtain ⟨a,k,v,w⟩:= h.invoice; refine ⟨a,k,v,?_⟩; filter_upwards [w,he] with t ht hr; rw [hr]; exact ht
lemma joins (h:Cookie G L f)(k:Cookie G L g) : Cookie G L (fun t=>f t + g t) := by
   obtain ⟨c,u,hc,H⟩:= h.invoice; obtain ⟨d,v,hd,H'⟩:= k.invoice
   refine ⟨c+d,u+v,add_nonneg hc hd,?_⟩; filter_upwards [H,H'] with x hx hy
   have hp : 1≤ p x:=Real.one_le_exp (sq_nonneg _); rw [add_mul]
   exact (abs_add_le ..).trans (add_le_add (hx.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (Nat.le_add_right u v)) hc)) (hy.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (by omega)) hd)))
lemma pays (h:Cookie G L f)(k:Cookie G L g) : Cookie G L (fun t=>f t * g t) := by
   obtain ⟨c,u,hc,H⟩:= h.invoice; obtain ⟨d,v,hd,H'⟩:= k.invoice
   refine ⟨c*d,u+v,mul_nonneg hc hd,?_⟩; filter_upwards [H,H'] with x hx hy
   rw [abs_mul]; exact (mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)).trans_eq (by rw [pow_add]; ring)
lemma const (x:ℝ): Cookie G L (fun _=>x):= bolt (Bolt.still _)
lemma pow (h:Cookie G L f)(j:ℕ): Cookie G L (fun x=> f x^j):= by
   induction j with
   | zero=> simp_rw [pow_zero]; exact const _
   | succ i ih=> simp_rw [pow_succ]; exact ih.pays h
lemma mast : Cookie G L (Delay.fineMonitor G L):= ⟨1,1,zero_le_one,Eventually.of_forall (fun x=> by have hp:= Delay.monitor_pos G L x; simp only [pow_one,one_mul]; exact (abs_of_pos hp).le)⟩
lemma lump (h:Cookie G L f)(k:Cookie G L g) (j:ℕ): Cookie G L (fun t=> clump j (f t) (g t)):=
   ((const _).pays k).pays ((const _|>.joins (((const _).joins h).pays (const 1))).pow j)
lemma expense (h:Cookie G L f)(j:ℕ): Cookie G L (fun t=> Courtyard.expense j (f t)) := by
   let h':=(((const 2|>.pays h).pays (const 2)|>.pays h).pays (const (3^j)))
   exact ((const 1).joins h').joins ((const 1).joins h')
lemma charged (h:Cookie G L f)(k:Cookie G L g)(j:ℕ): Cookie G L (fun t=> Lantern.fee j (f t) (g t)):= by
   let hu:= (const 1|>.joins h).joins k
   let hv:= ((hu.joins hu).lump h j)
   let hp:= k.pays (k.pays hv)
   exact (((h.joins h).joins (hp.joins hp)).joins (hv.joins hv))
end Cookie

/- explicit b radius for *normalized real expansion*, covers every actual β in the band
at the priced step. -/
def breath (G:Gauge)(L:Side) (x:ℝ):=2*(2*gStep (betaF G x L))
lemma funding (j:ℕ) (d:ℝ) {w Y:ℝ→ℝ}(h: Rate G L 0 w)(hc : Rate G L 0 Y) :
   ∀ᶠ t in atTop,
      let Z := betaF G t L; let b:= breath G L t; let D:=wick G L d t
      b ≤ eaves G L t ∧ b*Y t ≤ eaves G L t ∧ b ≤ 1 ∧
      Lantern.fee j (w t) D * (b*Y t) ≤ 1 ∧ (∀ β:ℝ, Z/2 ≤ β → gStep β < b) := by
   have ht : Rate G L (-(1/2)) (breath G L):= (glim G L).mul_left 2
   let X:= ht.mul hc
   have hf:= Lantern.fareRate j h (gen G L d) |>.mul X
   filter_upwards [contraction G L (a:=1) zero_lt_one ht (show -(1/2:ℝ) < vow by norm_num [vow]),
     contraction G L (a:=1) zero_lt_one X (show _ < vow from by norm_num [vow]), hf.below (by norm_num) 1 zero_lt_one, ht.below (by norm_num) 1 zero_lt_one,Delay.shift_pos G L] with t ht hx hr hZ hδ Z b D
   refine ⟨(by simpa only [one_mul] using! ht.le),(by simpa only [one_mul] using! hx.le),(le_abs_self _).trans hZ,(le_abs_self _).trans hr,fun β hv=>?_⟩
   obtain ⟨he,H⟩:= lamp G L hδ β hv; unfold b breath; linarith
lemma roots (x β:ℝ) (hx: 4 ≤ betaF G x L)(hg:0<β)(hv: β ≤ 2* betaF G x L) :
     (betaF G x L)^(-(1:ℝ))≤ gStep β ∧ (gStep β)⁻¹ ≤ betaF G x L:= by
   let y:= betaF G x L; have hy: 4 ≤ y := hx; have hu:0<y:=by linarith
   have hC: Real.sqrt β ≤ y:= by
      have hp:= Real.sqrt_nonneg β; have h:=Real.sq_sqrt hg.le; nlinarith
   have hp : (gStep β)⁻¹≤ y:=by simpa only [gStep,inv_inv] using hC
   exact ⟨by change y^(- (1:ℝ))≤_; rw [Real.rpow_neg hu.le,Real.rpow_one]; exact inv_anti₀ (Real.sqrt_pos.mpr hg) hC,hp⟩
end YM.RG01Estimate.Laplace
