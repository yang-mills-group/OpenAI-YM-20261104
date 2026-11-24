import YM.OPE.Compatible.Soup.Tarry
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop) (A U)
open Cinders Metric Set Zeph Jargon
open Crown Silt.Phere PertExtension Score Flock
variable {N:ChartRatio G} {s c:ℝ}(H:Sweep N s c) (x:∀ i,Bid.Dir G (n i))(P:Spells.Pad G)(g:ℂ→L[ℝ]ℝ)
include h
section
lemma Belt_E : Receipt β φ (fun j=> Belts (νsize A j)):= ((YM.OPE.Score.steady (8:ℝ) (carth h)).product (νGrow A h)).plus (YM.OPE.Score.steady 1 (carth h)) (carth h)
lemma Groom_E : Receipt β φ (fun j=> Spells.sizeQ (νsize A j)):=CashB h (νGrow A h)
lemma RedR {x:I→ℝ}(hx:Wax β φ x 0): Wax β φ (fun j=> RedG G (νsize A j) (x j)) 0:=by
       have he:= waitG h (νGrow A h); let L:= carth h; have hh(z:ℝ):=RateLE.const z L; let f:= (((hh 1).add hx L)); have hR:Wax β φ (fun i=>RoadK (νsize A i)) 0:= ((((hh 2).mul ((hh 4).mul he)|>.mono (by norm_num)).add (hh 2) L).add (hh 1) L); have hp(j:ℕ):Wax β φ (fun i=> Mā G j (νsize A i) (x i)) 0:= (((hh _).mul (hR.pow j L)).mul (f.pow j L)).mono (by simp); exact (hh 1).add (((hp 1).add (hp 2) L).add (hp 3) L) L
lemma OptQ {x:I→ℝ}(hx:Wax β φ x 0): Wax β φ (fun j=> Jfare (RedG G (νsize A j) (x j)) (TorC A P g j)) 0:=by
       have he:= RedR A h hx; have hp:= waitG h (TorFunds A h P g); let b:=carth h; have hh:= (hp.mul he).mono (le_of_eq (zero_add _)); exact (hp.add hh b).add (hh.add ((hp.mul (he.pow 2 b)).mono (by simp)) b) b
variable {A} {x:∀ i,Bid.Dir G (n i)} (hp:Lyd A φ x)
include hp
lemma Perc_A: Cinders.Feast (fun i=> ArtY A P g i (x i)) φ (Counters β):=by
       have he(j:Libra.Char.Phase) : Wax β φ (fun i=> (ArtY A P g i (x i)).seq j.val) 0 := RateLE.of_norm_le (OptQ A h P g (waitG h hp.brim)) (Eventually.of_forall (fun i=> AmpF A P g i (x i) le_rfl j)); exact ⟨he 0,he 1,he 2⟩ -- namespace
include H
lemma ripe_mark: Wax β φ (fun i=>g (ScoreX A i (EC A i (x i)))-(ArtY A P g i (x i)).atK (et A i)) (-(3/2)):=by
        let W(i):=2*et A i*‖x i‖; let B(i):=Belts (νsize A i); let u(i):=B i*W i; let C:=carth h; have hv: Receipt β φ (fun j=>2*‖x j‖*B j):=((YM.OPE.Score.steady (2:ℝ) C).product hp.brim).product (Belt_E A h)
        have ht:Tendsto u φ (𝓝 0):=(poseS A h hv).congr (fun i=>by unfold u W;ring) 
        let K(j):= sizeQ (νsize A j)*( (Barrier A j)⁻¹*u j)^ (2:ℕ); have he:Tendsto K φ (𝓝 0):=by
              let v(i):= (Barrier A i)⁻¹*u i; let ν:= Groom_E A h; have hc(i): v i=et A i/ Barrier A i*(2*‖x i‖*B i):=by unfold v u W; ring -- division
              have hy: Tendsto v φ (𝓝 0):=(haste A h hv).congr (fun i=> (hc i).symm); have hZ:Tendsto (fun i=> sizeQ (νsize A i)*v i) φ (𝓝 0):=(haste A h (ν.product hv)).congr fun i=>by rw[hc]; ring
              exact (zero_mul (0:ℝ)) ▸ ((hZ.mul hy).congr (fun i=>by unfold K v; ring))
        have hy:= Crown.krant (νsize A) G C (waitG h (νGrow A h)) (waitG h hp.brim) (waitG h (TorFunds A h P g)); apply RateLE.of_norm_le ((hy.mul ((poleV A h).pow 3 C)).mono (by norm_num)); filter_upwards [CapeF A h _ hp H,hymn A h,ht.eventually (ge_mem_nhds P.hB),he.eventually (ge_mem_nhds (show 0 < P.r^2/2 from by have hz:=P.pos; positivity))] with i hi hx hT hz
        have hh:0≤ W i:=mul_nonneg (mul_nonneg zero_le_two hx.1.le) (norm_nonneg _); let t:=TorC A P g i; let b:=νsize A i; refine (landscape (0:Site (n i)) P (hNu A i) _ (ScoreX A i) g _ (AuthCap A i) (x i) hx.1 hx.2 (W i) hh (fun j=>hi.2 _) (by omega) hT hz).trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx.1.le _)); let V:=charW 0 (x i); have h': 0≤ t:=TorPos A P g i; let B:= RedG G b ‖x i‖; let Y:=TagN (BFilm b V); have hY:Y ≤ B:=φpay (x i) le_rfl b; have ha:AuroraK b V ≤ Mā G 4 b ‖x i‖ := by
               exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (turnTime (x i) (4*b))) _) (by simpa only [Mā, add_zero,one_pow,mul_one] using Māhi G 4 b le_rfl)
        let S' := Mā G 4 b ‖x i‖; change Oxone Y (AuroraK b V) t ≤ Oxone B S' t; exact add_le_add (mul_le_mul_of_nonneg_left ha h') (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by norm_num) (zero_le_one.trans (VatR (BFilm b V)))) (mul_le_mul_of_nonneg_left hY (by norm_num)) _) (mul_nonneg (Nat.cast_nonneg _) h'))
lemma lens_law : Wax β φ (fun i=> g (signalF A i (EC A i (x i)))-(ArtY A P g i (x i)).atK (et A i)) Deb:=by
        have he: Wax β φ (fun i=>g (signalF A i (EC A i (x i)))-g (ScoreX A i (EC A i (x i)))) Deb:=by
           apply RateLE.of_norm_le (((RateLE.const ‖g‖ (carth h)).mul (LEDΛ A h)).mono (le_of_eq (zero_add _))); filter_upwards [flagFree A h _ hp H] with i hi; rw [← map_sub]; exact (g.le_opNorm _).trans (mul_le_mul_of_nonneg_left (stars_y A i _ hi) (norm_nonneg _))
        refine RateLE.congr (he.add ((ripe_mark h H P g hp).mono (by unfold Deb; norm_num)) (carth h)) (Eventually.of_forall fun i=> ?_); ring
end
end YM.OPE.Owl.HillZ
