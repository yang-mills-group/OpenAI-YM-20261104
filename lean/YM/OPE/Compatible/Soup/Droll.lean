import YM.OPE.Compatible.Soup.Roast
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
variable (h:Tendsto β φ atTop)
open Cinders Jargon Metric YM.PhysicalNext.Repeat.Aroma
section
variable {V:∀ j,Bid.Dir G (n j)} (A U)
lemma emigrant (i:I)(X:Config G (n i))(hp:Toss X (WorkB A i))(z: Palace G r): Toss (install (Punched A U i) X z) (WorkB A i):=by
        intro j hj; by_cases h : j ∈ fringe r (n i); swap; · rw [inF _ _ _ _ h] at hj; exact hp j hj
        obtain ⟨p,he,rfl⟩:= Finset.mem_image.mp h; obtain ⟨h,hp⟩:=arcP (Finset.mem_sdiff.mp he).1; rw [← pier]; exact ⟨(aery (Punched A U i) h).trans (broader A U i),(aery (Punched A U i) hp).trans (broader A U i)⟩
lemma chantR (j:I)(x z:ℝ)(hv:0 ≤ x)(W:Config G (n j))(hk:0 ≤ z)(B:Palace G r)(ht:∀ i,G.chord (W i)≤ x)(hy:B∉ Zeph.Chamber G (fieldP r) ((CloudH.taxC r)*(x+z))): ∃ u:Face (Per (n j)),z ≤ G.chord (faceValue (install (Punched A U j) W B) u):=by
       let Y:=install (Punched A U j) W B; by_contra h; push Not at h; have he : CloudH r x z Y:= ⟨hv,hk,(fun e hi=> by rw [show Y e=W e from inF _ _ _ _ hi]; exact ht e),fun i _=>(h i).le⟩; apply hy; intro i; exact (inSeat _ W B i ▸ CloudH.cup (Volta A U j) he (dig _ i)) -- check implicit
private lemma luck (j:I)(G':ℝ) (h:0<et A j)(hz:Bounty A j=((et A j)^2)⁻¹):τRG S.clip*(G')^2=τRG S.clip*Bounty A j*((et A j)*G')^2:=by rw [hz]; field_simp
lemma beam_z (j:I)(W:Config G (n j))(he:Toss W (WorkB A j))(hh:0< et A j)(hv:Bounty A j=((et A j)^2)⁻¹)(G':ℝ)(ht:0≤G')(hc:et A j*G'≤ Barrier A j) (f:Face (Per (n j)))(hz: et A j*G' ≤ G.chord (faceValue W f)) : CoinΩ A j W ≤ -τRG S.clip*(G')^2+loopsΩ A j + stat A j:=by
       have hg:0 ≤ Bounty A j:=by rw [hv]; positivity
       let Y:= (Stru A j); let P:= Y.path.inChannels Y.clip Y.p Y.beta W; have hp : τRG S.clip* (G')^2 - loopsΩ A j ≤ P:=by unfold P Y; rw [gaugesK A j,trueB A j,luck A j G' hh hv]; exact chop W he (Walt A j) hg (mul_nonneg hh.le ht) hc f hz
       have hm:= (abs_le.mp (BoxΘ A j W he)).1; have hu: CoinΩ A j W= -P-WeightE A j W:=by unfold CoinΩ PriceΩ Eyrie.rhoE P Y Rep.exponent WeightE Meta Stru; ring
       rw [hu]; linarith only[hp,hm]
include h
variable {A}
open Zeph
noncomputable abbrev trimX (s x:ℝ)(p:ℝ):ℝ:= x+(1+p)^2/s
omit h in private lemma qReach (s t:ℝ)(hs:0<s)(ht:0 ≤ t): t ≤ s*(1+t*s⁻¹)^2:=by
        let x:=1+t*s⁻¹; have he: 1 ≤ x:=le_add_of_nonneg_right (mul_nonneg ht (inv_pos.mpr hs).le); calc
             _ = s*(x-1):=by unfold x;field_simp;ring
             _ ≤ s*x^2:=mul_le_mul_of_nonneg_left (by nlinarith only[he]) hs.le
private lemma liteA : Receipt β φ (stat A):= YM.OPE.Score.bound 1 (carth h) ((((ΩH A h).tends (by norm_num [Deb]) (carth h)).norm).eventually (ge_mem_nhds (by simp))) -- implicit A cannot infer? in target
variable {N:ChartRatio G}{s a:ℝ}(H:Sweep N s a)
include hs H
variable {U} (V:∀ j,Bid.Dir G (n j))(P:I→ℝ)
lemma biasQ (U:Scaffold φ (Counters β) n (Mnd i S A) r)(hp:Lyd A φ V)(ht:Receipt β φ P):∃ T:I→ℝ,Receipt β φ T ∧∀ᶠ i in φ, 0 ≤ T i ∧ ∀ z: Palace G r, z ∉ Zeph.Chamber G (fieldP r) (et A i*T i) → PriceΩ A i (install (Punched A U i) (EC A i (V i)) z)-PriceΩ A i (EC A i (V i)) ≤ -‖P i‖:=by
        let k:=τRG S.clip; have hk:0 < k:=τRGP; let m:=CloudH.taxC r; have hm:0 ≤ m:=zero_le_one.trans (CloudH.taxNL r); let W(i):=EC A i (V i); let F(i):=CoinΩ A i (W i); let v(i):=‖F i‖ + ‖loopsΩ A i‖ + ‖stat A i‖ + ‖P i‖; have hy(q:I→ℝ)(hh:Receipt β φ q): Receipt β φ (fun i=>‖q i‖):=hh.liftp (Eventually.of_forall fun i=> show ‖‖q i‖‖ ≤ ‖q i‖ from (norm_norm _).le); let q:=carth h; have he: Receipt β φ v:= (((hy F (roast hs h hp H)).plus (hy _ (scoreLoop A h)) q).plus (hy _ (liteA (A:=A) h)) q).plus (hy P ht) q -- Binder scoreLoop?
        let w(i):=1+v i*k⁻¹; let Z(i):= m*(2*‖V i‖+w i); have hs(c:ℝ):= YM.OPE.Score.steady c q; have hz:Receipt β φ w:=(hs 1).plus (he.product (hs k⁻¹)) q; refine ⟨Z,(hs m).product (((hs 2).product hp.brim).plus hz q),?_⟩
        filter_upwards [hymn A h, rentGate A h hz, CapeF A h V hp H,ηO A h,hp.habit] with i hi hv hh hV hp'; have hg: Toss (W i) (WorkB A i):=SerT.actual (hp'.gauge _); have ha:0 ≤ v i:=by unfold v; positivity
        have hw:1 ≤ w i:=le_add_of_nonneg_right (mul_nonneg ha (inv_pos.mpr hk).le); have h' := hi.1; refine ⟨mul_nonneg hm (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (zero_le_one.trans hw)),fun p ht=>?_⟩
        let B₀:=2*et A i*‖V i‖; have hZ:0≤w i:=zero_le_one.trans hw; obtain ⟨u,hy⟩:= chantR A U i B₀ (et A i*w i) (by unfold B₀; positivity) (W i) (mul_nonneg hi.1.le hZ) p hh.2 (by rw [show CloudH.taxC r * _= et A i*Z i from ?_]; exact ht; unfold Z B₀ m; ring)
        let Q:=install (Punched A U i) (W i) p; have hh': CoinΩ A i Q ≤ _:= beam_z A i Q (emigrant A U i (W i) hg p) hi.1 hV.1 _ hZ hv u hy; have ht: v i ≤ k*(w i)^2 := qReach k (v i) hk ha; change PriceΩ A i Q-PriceΩ A i (W i) ≤ _; rw [show PriceΩ A i Q-PriceΩ A i (W i)= CoinΩ A i Q-F i from by unfold F CoinΩ; ring]; change CoinΩ A i Q ≤ -k*(w i)^2+_+_ at hh'
        have hV: -‖F i‖ ≤ F i:=neg_abs_le _; unfold v at ht; linarith only[ht,hh',hV,Real.le_norm_self (loopsΩ A i),Real.le_norm_self (stat A i)]
end
end YM.OPE.Owl.HillZ
