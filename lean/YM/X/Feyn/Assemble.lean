import YM.X.Feyn.Paint
/-!
First-degree tally in the input diagram, including current Haar density and denominator. Normalize first two only. No rate.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set MeasureTheory Gauge Lattice Wilson PertExtension PertExtension.Chart PertExtension.Orb Precision
open Pert.Orb (Potential positiveLinks takeLink wilson)
open Series Series.Radial Series.Tested GaussianScore Gauss
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (he:Even n.val) {i:ℕ}
local notation "E" => Potential G n
local notation "A₁" => Dir G n
lemma duo (f g:ℕ→ℝ)(hi:∀ j < i,f j=0): ∑ p∈ Finset.antidiagonal (i+1),f p.1 * g p.2=f (i+1)* g 0+ f i*g 1:= by
    let p:= (i+1,0); rw [← Finset.sum_erase_add (a:=p) _ _ (Finset.mem_antidiagonal.mpr (by unfold p; simp)), Finset.sum_eq_single_of_mem (i,1), add_comm]
    · refine Finset.mem_erase.mpr ⟨?_,Finset.mem_antidiagonal.mpr rfl⟩; unfold p; simp
    rintro ⟨u,v⟩ h H; have hA:=Finset.mem_erase.mp h; have hB:=Finset.mem_antidiagonal.mp hA.2; have hv: u < i:= by
        by_contra! hk; obtain rfl|h' := eq_or_lt_of_le hk; exact H (Prod.ext rfl (by omega)); exact hA.1 (by ext1<;>(unfold p; omega))
    rw [hi u hv,zero_mul]
lemma pool {f g:A₁→ℝ}(hf:ContDiffAt ℝ ω f 0)(hg:ContDiffAt ℝ ω g 0)(z:A₁)(h:∀ j < i, jet f j=0) : jet (f*g) (i+1) z=jet f (i+1) z*jet g 0 z+jet f i z*jet g 1 z:= by
   have he:= (directions (hf.of_le (m:=∞) le_top) z).prod (directions (hg.of_le (m:=∞) le_top) z); have hh:= directions (f:=f*g) ((show ContDiffAt ℝ ω (f*g) 0 from hf.mul hg).of_le le_top) z
   have ht:=congr_fun (hh.unique he) (i+1); simp only [Tested.conv,Tested.term, PowerSeries.coeff_mul,PowerSeries.coeff_mk] at ht; rw [ht]; exact duo (fun i=>jet f i z) (fun i=>jet g i z) (fun j hj=>congr_fun (h j hj) _)

abbrev rent (T:ChartRatio G):A₁→ℝ:= jacobian T
private lemma start_exp {z:A₁}: expsum (Radial.layers fiscal) 1 1 z = -jet fiscal 3 z:= by
   simp [expsum,Radial.layers,Zone.TaylorPow,Zone.mul, Finset.sum_range_succ,show Finset.antidiagonal 1={((0,1):ℕ×ℕ),(1,0)} from rfl]
variable {T:ChartRatio G}(R:LocalRatio T) {O: Config G n→ ℝ}

-- formula before projection
local notation "ν"=> tangent G (Cotree n)
variable (h:ContDiffAt ℝ ω (O ∘ representative) 0)(hO:LocalTest (restrictedO O))(hp:RadialOrder i (O ∘ representative))
include h hO hp he R
lemma treeOne (hW:gaussian (G:=G) he (jet (O ∘ representative) i * jet (rent T) 1)=0): diagonalWith T (restrictedO O) (i+1) = gaussian he (jet (O ∘ representative) (i+1) - jet (O ∘ representative) i * jet fiscal 3):= by
   let U:=restrictedO O; let w:= O ∘ representative; let D:= jet w (i+1)- jet w i*jet fiscal 3; let q:= rowsWith T (1:Observable G n)
   have hd: diagonalWith T U (i+1)* q 0=rowsWith T U (i+1):= by
      have hh:=congr_fun (rows_with_head R he U) (i+1); simp only [Tested.conv,Tested.term, PowerSeries.coeff_mul,PowerSeries.coeff_mk] at hh
      rw [duo (diagonalWith T U) _ (diag_down R hO hp he),rowsWith_odd (k:=1) _ (Nat.odd_iff.mpr rfl),mul_zero,add_zero] at hh; exact hh
   have hz : ∀ j < i, jet w j=0:=fun j hj=> Tested.jets_vanish (by exact hO.germ) hp hj -- namespace
   let L:= (∫ x:A₁,kernel fiscal x ∂tangent G (Cotree n)); have hb : q 0=rent T (n:=n) 0*L:= (rows_zero ..).trans (by rw [Pi.one_apply,mul_one])
   have hg : 0<q 0:= pivot he R
   have hs := rows_gaussian T U (i+1) he
   let J:= jet (accountingWith T U); have HA : integrandSeries fiscal (accountingWith T U) (i+1)=(rent T (n:=n) 0) • D + jet w i* jet (rent T) 1:= by
      funext x
      have ht j (hj:j ≤ i): J j x=if j=i then rent T (n:=n) 0*jet w i x else 0:= entering_jets R hO hp j hj x
      have ht' : accountingWith T U = w * rent T:= funext (fun x=>mul_comm _ _)
      change (∑ p∈ Finset.antidiagonal (i+1),J p.1 x*expsum (Radial.layers fiscal) p.2 p.2 x)=_; rw [duo (fun j=>J j x) (fun j=>expsum (Radial.layers fiscal) j j x) (fun j hj=> ?_)]
      · rw [(ht i le_rfl),if_pos rfl]; change J (i+1) _ * expsum _ 0 0 x + (rent T (n:=n) 0 *jet w i x)* expsum _ 1 1 x= _; unfold J; rw [ht',pool h (Chart.Ratio.jacobian_smooth R) x hz,start_exp (G:=G)]
        rw [show expsum _ 0 0 x=1 from (by unfold expsum;simp [Zone.TaylorPow])]; simp only [mul_one,jet_zero, Pi.add_apply,Pi.smul_apply,D,Pi.sub_apply, Pi.mul_apply,smul_eq_mul];ring
      rw [ht j hj.le,if_neg hj.ne]
   change L*gaussian he _= _ at hs; rw [HA] at hs
   have hp' : Plausible D:=(Plausible.stamp _ _).sub ((Plausible.stamp _ _).mul (Plausible.stamp _ _))
   rw [show gaussian he (_+_) = _ + _ from average_add (saddle he) _ (hp'.scale (rent T (n:=n) 0)) ((Plausible.stamp w i).mul (Plausible.stamp (rent (n:=n) T) 1))] at hs -- stamp n param?
   change L*(gaussian he (_ • D)+gaussian he (jet w i* jet (rent T) 1))= _ at hs
   rw [hW, add_zero,show gaussian he (_ • D)=(rent T (n:=n) 0)*gaussian he D from average_scale ..] at hs; rw [hb] at hg hd; apply mul_right_cancel₀ hg.ne'; rw [hd, ←hs];ring
end YM.PositionX.Feyn
