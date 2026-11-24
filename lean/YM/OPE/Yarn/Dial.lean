import YM.OPE.Yarn.Neutral
/-!
# Equation at an appointed stop vs moving parent. Heights NOT tied.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J U : Type}[Fintype J][DecidableEq J]{G:Gauge}{C:Family G} {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ) {d m p N:ℕ}
variable {T X y c x t : I→ℝ} {k n:I→ℕ} {a b:ℝ} {φ:Filter I}
set_option quotPrecheck false
local notation "P" => C.path
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "w"=> C.path.levels
local notation "Q"=> C.path.levels.clock.hatBeta
local notation "u"=> C.S.a
variable (d) -- binder override
variable (hr:Height C.S φ T k a)(ht:Tendsto T φ atTop)
include hr ht
include H
lemma plus1 : Coins φ T (fun i=>1+(C.path.levels.params (k i)).columns):= by
   refine Coins.by_le ((Bill.const _ ht).add (columns_p ht H.cuts.toPackage.toTableTickets hr|>.up) ht) (Eventually.of_forall fun i=>?_); exact (le_add_of_nonneg_right (zero_le_one.trans ((w).params _).columns_ge)).trans (Real.le_norm_self _)
lemma wax_price (l b:ℕ) (hb:0<b) : Coins φ T (fun i=>wax C b (radiusCost C l (k i)) (k i)) := Coins.mul (license_polynomial ht hr l H.cuts hb) (near_coins ht hr)
omit H in
lemma tar_coins (h:Bi φ T x y): Bi φ T (fun i=>tarred C (k i) (x i)) y:=by simpa only [tarred,div_eq_mul_inv,mul_one] using! Bi.mul h (Coins.inv (Coins.mul (Bi.const (16:ℝ) (by norm_num) ht) (hat_price ht (hr.step (w).fits.mesh))))
-- allow c factor positive pos from e.g. w* in basis. smoothing extra.
local notation "e" i => ebb C d (k i) (x i)
local notation "E" i => u (k i)^d/(y i)
variable (h:Bi φ T x y) (hx:∀ᶠ i in φ,y i≠0)
include H h hx
lemma ebb_bi : Bi φ T (fun i=>ebb C d (k i) (x i)) (fun i=>C.S.a (k i)^d / y i):=by
   let x':= shift_mesh ht hr H.cuts.tabs; let v:= hat_price ht (hr.step (w).fits.mesh)
   have hh : Bi φ T (fun i=> 4*(1/x i)) (fun i=>(y i)⁻¹):=by simpa only [one_mul,one_div] using Bi.mul (Bi.const (4:ℝ) (by norm_num) ht) (h.inv hx)
   unfold ebb; simpa only [one_mul,div_eq_mul_inv] using! Bi.mul (Coins.mul (Bi.const (4:ℝ) (by norm_num) ht) (plus1 H hr ht)) (Bi.mul (Bi.const (2:ℝ) (by norm_num) ht) (Bi.mul (x'.power ht d) (Bi.mul v hh)))
variable {a' : ℝ} (hn:Height C.S φ T n a')
local notation "S" i => C.S.a (n i)^d
local notation "z" i => ((C.S.a (n i)/C.S.a (k i))^d*y i)
include hn
lemma full_price (l B:ℕ)(hb:0<B) (hp : ∀ᶠ i in φ, 0<x i ∧ C.ref d ≤ n i∧ n i≤ k i): Bi φ T (fun i=>submit C d B (radiusCost C l (k i)) (n i) (k i) (x i)) (fun i=> ((C.S.a (n i)/C.S.a (k i))^d*y i)):=by
    have hg:∀ᶠ i in φ,(z i) ≠0:= by filter_upwards [hx] with i hi using mul_ne_zero (pow_ne_zero _ (div_ne_zero (C.S.a_pos _|>.ne') (C.S.a_pos _|>.ne'))) hi
    let s i:= ((C.S.a (n i)/C.S.a (k i))^d * y i); let A i:= max1 C d (n i) (k i) (x i); let L i:= Loom.max2 C d (n i) (k i) (x i)
    have hZ: Bi φ T A s:= by
       unfold A max1; simp_rw [div_eq_mul_inv (x _)] -- first term
       refine (Bi.mul (Bi.mul (Bi.mul (renal_coins ht hr) (Bi.mul h (Coins.inv (Coins.mul (Bi.const (16:ℝ) (by norm_num) ht) (hat_price ht (hr.step (w).fits.mesh)))))) (Bi.refl φ T _)) (Coins.div (fly_coins ht hn d) (fly_coins ht hr d))).congr (EventuallyEq.refl ..) (Eventually.of_forall fun i=>?_)
       unfold s; ring
    have hZ': Bi φ T L s:= by
       have hl:Bi φ T (fun i=> ‖alto P (n i) d‖) (fun i=>(C.S.a (n i)^d)⁻¹):= by simp_rw [alto_norm]; exact Bi.refl ..
       let Z' i:= (C.S.a (n i)^d)⁻¹*(E i); have hE:Bi φ T (fun i=> (64*(1+(C.path.levels.params (k i)).columns)*‖alto P (n i) d‖)*e i) Z' :=by simpa only [one_mul] using! Bi.mul (Bi.mul (Coins.mul (Bi.const (64:ℝ) (by norm_num) ht) (plus1 H hr ht)) hl) (ebb_bi H d hr ht h hx)
       have hh:∀ᶠ i in φ,Z' i≠0:=by filter_upwards [hx] with i hi; exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (C.S.a_pos _|>.ne'))) (div_ne_zero (pow_ne_zero _ (C.S.a_pos _|>.ne')) hi)
       apply (Bi.div (fly_coins ht hn d) hE hh).congr (EventuallyEq.refl ..) (Eventually.of_forall ?_); intro i; unfold s Z'; rw [div_pow]; simp only [one_div,mul_inv_rev,inv_div,inv_inv]; ring
    let W i:= (A i)⁻¹+(L i)⁻¹; have he : Bi φ T W (fun i=>(s i)⁻¹):=by
       refine ⟨(Bill.add (hZ.inv hg).up (hZ'.inv hg).up ht), ((hZ.inv hg).down).mono ?_⟩; filter_upwards [hp] with i ⟨hi,hq,hv⟩; apply le_trans _ (Real.le_norm_self (W i)); refine le_trans (le_of_eq (Real.norm_of_nonneg (inv_nonneg.mpr (max1_pos H.cuts d _ hq hi hv|>.le)))) (le_add_of_nonneg_right (inv_nonneg.mpr ?_)); exact (max2_pos H.cuts d _ hq hi |>.le)
    have hh := he.inv (hg.mono fun i hi=> inv_ne_zero (a:=s i) hi); simpa only [submit,mul_one,inv_inv] using! Bi.mul hh (wax_price H hr ht l B hb)
omit hn in
lemma submit_fixed (l B:ℕ)(hb:0<B)(hm:C.ref d ≤ m)(hv:∀ᶠ i in φ,y i> 0)(hp:∀ᶠ i in φ,0<x i): Bill φ T (fun i=>(submit C d B (radiusCost C l (k i)) m (k i) (x i))⁻¹) (fun i=>C.S.a (k i)^d /y i):=by
   simp_rw [submit,mul_inv_rev]; refine (Cheap.times (Coins.inv (wax_price H hr ht l B hb)|>.up) (Loom.bprice H.cuts d m hm ht hr (hv.mono fun i hi=> inv_pos.mpr hi) (Bi.up (h.inv hx)) hp)).congr (EventuallyEq.refl ..) (Eventually.of_forall ?_); intro i; change _*_=_; rw [mul_comm]; exact (div_eq_mul_inv ..).symm
end YM.OPE.Yarn

