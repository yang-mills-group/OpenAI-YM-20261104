import YM.OPE.Compatible.Soup.Dune
/-!
# Polling the actual chamber Dir
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant.Aloof
set_option maxHeartbeats 200000
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset Sleeve
open Silt Libra Coin Rill Silt.Float Variance Votive PertExtension Series GaussianScore Radial Next.Foundations
variable {G:Gauge}{b i j k r:ℕ}{n:Side}
variable {v s a c c':ℝ}{p:Clip}{Z:PathData G}
open Next.Free Next.Scheduling
variable {K:Sponsor G}{T:Seasons K}
open Merchant.SiteL
section
variable (G)(hp:Board n (r+1))
lemma sparse_s (x: Chamber G r): SerT (sailT G hp x) (r+1):=by
       intro i hi; have ht:i∈ fringe r n:= not_not.mp (fun h=>hi (silly G hp x i h)); obtain ⟨y,hY,rfl⟩:= mem_image.mp ht; have hz:= arcP (mem_sdiff.mp hY).1; refine ⟨aery hp hz.1,?_⟩; rw [← pier]; exact aery hp hz.2
lemma money_s (x:Chamber G r): ‖sailT G hp x‖≤‖x‖:=by
       refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>?_ ; obtain ⟨y,rfl⟩:= arkSur i; exact ebbNorm G hp x y
lemma money_pin (x:Bid.Dir G n):‖PinT (r:=r) G x‖≤‖x‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _i=>show ‖x _‖≤_ from norm_le_pi_norm ..
lemma sky_t (x:Bid.Dir G n)(Z:Law (Chamber G r))(f:Bid.Dir G n→ℝ) (r':ℕ)(hv:r+1≤r')(ht:SerT x r'): SerT (mate (sailT G hp) (chrom f) Z x) r':=by
       unfold mate; rw [_root_.sub_apply, ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply, sub_eq_add_neg]; rw [← (sailT G hp).map_neg]; exact ht.plus ((sparse_s G hp _).raise hv)
end
variable (A:Alps K T i c)(hs:G.Simple)
section
variable {p:G.Color}
variable (hp:Board n (r+1))(U:Law (Chamber G r))
lemma chrom2 (x:Bid.Dir G n)(f:Bid.Dir G n→ℝ): chrom f x x=2*jet f 2 x:=by
       rw[podium]; have hx: ![x,x]=(fun _: Fin 2=>x):= funext fun i=>by fin_cases i <;> rfl
       unfold jet;rw [hx]; norm_num [Nat.factorial]; ring
variable (hU: SiteL (sailT G hp) (chrom (Dune A)) U)(hv:r+1 ≤ b) (x:Bid.Dir G n)
-- absolute checker on the whole patch.A_len independent of amplitudes
lemma combB (f:Bid.Dir G n→ℝ)(H:∀ x:Bid.Dir G n,SerT x b→∀ a:ℝ,‖x‖<a→ Past f x 2 a c')(hF:ContDiffAt ℝ ω f 0)(x z:Bid.Dir G n)(hx:SerT x b)(ha:‖x‖ ≤ a)(hy:SerT z b)(hh:‖z‖≤1)(ht:0 ≤ c') : chrom f x z ≤ 2*((a+2)^2)*c':=by
        let R:=chrom f
        have hr:SerT (-z) b:= by simpa only [neg_one_smul] using hy.gauge (-1)
        have hx':0 < a+2:=by have h:= (norm_nonneg _).trans ha; linarith only[h]
        have hS : ‖x+z‖ < a+2:=(norm_add_le ..).trans_lt ((add_le_add ha hh).trans_lt (by linarith))
        have hZ : ‖x+-z‖ < a+2:=(norm_add_le ..).trans_lt ((add_le_add ha ((norm_neg _).trans_le hh)).trans_lt (by linarith))
        obtain ⟨_,h1⟩:=abs_le.mp (Pat_charge (i:=2) hF (H (x+z) (hx.plus hy) _ hS) two_pos le_rfl hx'.le ht); obtain ⟨h0,_⟩:=abs_le.mp (Pat_charge (i:=2) hF (H (x+-z) (hx.plus hr) _ hZ) two_pos le_rfl hx'.le ht)
        have hi: R (x+z) (x+z)-R (x+-z) (x+-z)=4 * R x z:=by simp only [map_add,map_neg,LinearMap.add_apply, LinearMap.neg_apply]; rw [show R z x=R x z from turnsT f (hF.of_le le_top) z x]; ring
        have ht' : 0 ≤ (a+2)^2*c':=(by positivity); rw[show R (x+z) (x+z)=2*jet f 2 (x+z) from chrom2 .., show R (x+-z) (x+-z)= 2*jet f 2 (x+-z) from chrom2 ..] at hi; change R x z ≤ _; change jet f 2 (x+z)≤_ at h1; change _ ≤ jet f 2 (x+-z) at h0; linarith only[ht',h0,h1,hi]
include hU hv hs
omit hU in lemma polar (H:∀ x:Bid.Dir G n,SerT x b→∀ a:ℝ,‖x‖<a→ Past (Dune A) x 2 a c') (x:Bid.Dir G n)(hx:SerT x b)(ha:‖x‖ ≤ a) (p: Chamber G r)(he:‖p‖≤1)(ht:0 ≤ c') : chrom (Dune A) x (sailT G hp p) ≤ 2* ((a+2)^2)*c' :=
         combB (Dune A) H (DuneAt A hs).sm x (sailT G hp p) hx ha (SerT.raise (sparse_s G hp p) hv) (le_trans (money_s G hp p) he) ht
omit hU in lemma gustB (H:∀ x:Bid.Dir G n,SerT x b→∀ a:ℝ,‖x‖<a→ Past (Dune A) x 5 a c') (hX:SerT x b)(ha:‖x‖ ≤ a) (he:0≤ c')(d:ℝ)(hd:0<d)(ht:∀ x,d*‖x‖^2 ≤ U.P x x) : ‖pour (sailT G hp) (chrom (Dune A)) U x‖ ≤ (2*(a+2)^2*c')/d :=by
         let R:=sailT G hp; let g:=pour R (chrom (Dune A)) U x; by_cases hy: g=0; · rw [show pour R (chrom (Dune A)) U x=0 from hy,norm_zero]; positivity
         let y:=‖g‖⁻¹ • g; have hY:0<‖g‖:= norm_pos_iff.mpr hy; have hz:‖y‖=1:=by unfold y; rw[norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hY.le),inv_mul_cancel₀ hY.ne']
         have he': ∀ x:Bid.Dir G n,SerT x b→∀ a:ℝ, ‖x‖<a → Past (Dune A) x 2 a c':=by intro x hx a ha; obtain ⟨hg',hh⟩:= H x hx a ha; exact ⟨hg',fun i ht hp=>hh i ht (hp.trans (by norm_num))⟩
         have hg:= polar A hs hp hv he' x hX ha y hz.le he; rw [loan] at hg; change U.P g y ≤ _ at hg; have h : U.P g y=U.P g g / ‖g‖:=by unfold y; rw [map_smul,smul_eq_mul,div_eq_inv_mul]
         rw [h,div_le_iff₀ hY] at hg; change ‖g‖≤_; rw [le_div_iff₀ hd]; apply le_of_mul_le_mul_right _ hY; exact (show ‖g‖*d*‖g‖=d*‖g‖^2 from by ring).trans_le ((ht g).trans hg)
end
end YM.OPE.Merchant.Aloof
