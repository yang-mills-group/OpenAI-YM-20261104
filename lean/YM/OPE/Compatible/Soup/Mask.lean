import YM.OPE.Compatible.Soup.Lark
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
variable (A)
noncomputable abbrev BoxAmt (j:I) :ℝ:= ((↑(((WorkB A j+ WorkB A j+1)^4):ℕ)):ℝ)
noncomputable abbrev stat (j:I) :ℝ:= BoxAmt A j * (est (Meta A j) S.supportExponent*ℰb (β j))
noncomputable abbrev WeightE (j:I)(x:Config G (n j)):= (Stru A j).activities.additive (Meta A j) x
noncomputable abbrev PriceΩ (j:I)(x:Config G (n j)):= (Stru A j).exponent x
noncomputable abbrev CoinΩ (j:I)(x:Config G (n j)):= PriceΩ A j x - rhoE (Stru A j)
lemma BoxΘ (j:I)(W:Config G (n j))(h:Toss W (WorkB A j)) : ‖WeightE A j W‖ ≤ stat A j := extraE W h (A j).gen.lawful.labels S.price_pos (A j).gen.TagQ.width.symm.le
noncomputable abbrev Deb:= -(11/10:ℝ)
include h
lemma ωMint : Receipt β φ (BoxAmt A):=by let K:=carth h; let p:= MintW A h; unfold BoxAmt; simp_rw [Nat.cast_pow,Nat.cast_add (WorkB A _+ WorkB A _),Nat.cast_add (WorkB A _),Nat.cast_one]; exact YM.OPE.Score.power _ ((p.plus p K).plus (YM.OPE.Score.steady _ K) K) K
lemma ΩH : Wax β φ (stat A) Deb:=by
        have hp:Receipt β φ (fun j=> est (Meta A j) S.supportExponent):=by
            let K:=carth h; have hv(t:ℝ):Receipt β φ (fun _=>t):=YM.OPE.Score.steady t K; let x:= (coverPs h).plus (hv 1) K; let u:=x; unfold est; simp_rw [show ∀j : I,(Meta A j).B=coverJ (β j) from fun j=>(A j).gen.TagQ.epoch]; exact (((hv 12).product x|>.power 4 K).product (hv _))
        have ht: Wax β φ (fun j=> BoxAmt A j * (est (Meta A j) S.supportExponent*ℰb (β j))) (0+(0+ -(11/10))) := (waitG h (ωMint A h)).mul ((waitG h hp).mul (Φmask h)); exact ht.mono (by norm_num [Deb])
noncomputable abbrev Kexp (j:I)(x:Bid.Dir G (n j))(k:ℕ):=∑ i∈range (k+1), (et A j)^i*jet (KPole A j) i x
noncomputable abbrev Lexp (j:I)(x:Bid.Dir G (n j))(k:ℕ):=∑ i∈range (k+1), (et A j)^i*jet (LPole A j) i x
variable (x:∀ j,Bid.Dir G (n j)) (hp:Lyd A φ x)
variable {A x}
include hp
lemma wagerE : Wax β φ (fun j=> WeightE A j (EC A j (x j))) Deb:= by refine (ΩH A h).of_norm_le ?_; exact hp.habit.mono fun i hi=>BoxΘ A i _ (SerT.actual (hi.gauge _))
include hs
lemma bringK (he:k+1 ≤5): Wax β φ (fun j=> KPole A j (et A j • x j)-Kexp A j (x j) k) ((↑(k+1:ℕ):ℝ)*(-(1/2))):=by
        obtain ⟨f,g,Y⟩:=merit A h; let u(j:I):= ‖x j‖+1; have hz(j:I):‖x j‖<u j:=lt_add_one _; have hu:Receipt β φ u:= hp.brim.plus (YM.OPE.Score.steady _ (carth h)) (carth h)
        have hy:= (waitG h ((hu.power (k+1) (carth h)).product Y.meat)).mul ((poleV A h).pow (k+1) (carth h)); refine RateLE.of_norm_le (hy.mono (by norm_num)) ?_; filter_upwards [hp.habit,hymn A h] with i hi hh; exact billH (Variance.DuneAt (Mater A i) hs).sm (Y.ν i (x i) hi _ (hz i)).1 he hh.1 ((norm_nonneg _).trans (hz i).le) (Y.fare i).1
lemma bringL (he:k+1≤5): Wax β φ (fun j=> LPole A j (et A j • x j)-Lexp A j (x j) k) ((↑(k+1:ℕ):ℝ)*(-(1/2))):=by
        obtain ⟨f,g,Y⟩:=merit A h; let u(j:I):= ‖x j‖+1; have hz(j:I):‖x j‖<u j:=lt_add_one _; have hu:Receipt β φ u:= hp.brim.plus (YM.OPE.Score.steady _ (carth h)) (carth h)
        have hy:= ((waitG h (hu.power (k+1) (carth h))).mul Y.lite).mul ((poleV A h).pow (k+1) (carth h)); refine RateLE.of_norm_le (hy.mono (by norm_num)) ?_; filter_upwards [hp.habit,hymn A h] with i hi hh; exact billH (Variance.DuneAt (Mater A i) hs).sg (Y.ν i (x i) hi _ (hz i)).2 he hh.1 ((norm_nonneg _).trans (hz i).le) (Y.fare i).2
open Zeph
variable {N:ChartRatio G} {s c:ℝ}(H:Sweep N s c)
omit h hp hs in lemma goodness (j:I)(x:Bid.Dir G (n j))(h:flags (Barrier A j) (EC A j x)=∅) : CoinΩ A j (EC A j x)= -(Bounty A j)*KPole A j (et A j • x)-LPole A j (et A j • x)-WeightE A j (EC A j x) := by
       let y:=EC A j x; let V:=Stru A j; unfold CoinΩ PriceΩ Rep.exponent rhoE;change _ - V.path.inChannels _ _ _ y-_ -_ =_; have he:= ciel (Mater A j) (Meta A j) (et A j • x) V.beta h; rw [show V.path=Haslt A j from gaugesK ..,show (Stru A j).clip=(Mater A j).clip from (trueB ..).trans (capB ..).symm,show (Haslt A j).inChannels _ _ _ y=_ from he]; change _= -(Bounty A j)*KPole A j _ - LPole A j _-_ ; unfold Bounty WeightE KPole LPole Meta; unfold V Stru; ring
include H
variable (A)
-- script for exponent excluding jac
noncomputable def PolV (j:I)(x:Bid.Dir G (n j)):Token:= ⟨-jet (KPole A j) 2 x,-jet (KPole A j) 3 x-jet (LPole A j) 1 x,-jet (KPole A j) 4 x-jet (LPole A j) 2 x⟩
variable {A}
omit h H hp in lemma polH (j:I)(x:Bid.Dir G (n j))(hp:Bounty A j=((et A j)^2)⁻¹)(hr:0 <et A j): -(Bounty A j)*Kexp A j x 4-Lexp A j x 2=(PolV A j x).atK (et A j):=by
       let V:=Mater A j; have ht:jet (KPole A j) 0 x=0:= (Variance.DuneAt V hs).zero _ _ (by omega); have hk:jet (KPole A j) 1 x=0:= (Variance.DuneAt V hs).zero _ _ (by omega); have hh:jet (LPole A j) 0 x=0:=(jet_zero ..).trans (unit_at V (Meta A j) _).2; unfold Lexp Kexp PolV JetS.atK; rw [hp]; simp only [sum_range_succ,hk,hh,ht,sum_range_zero,mul_zero,zero_add,pow_one,smul_eq_mul]; field_simp; ring
lemma pricePol : Wax β φ (fun i=> CoinΩ A i (EC A i (x i))-(PolV A i (x i)).atK (et A i)) Deb:=by
       let P:=bringK (k:=4) hs h hp (by omega); have hG:=bringL (k:=2) hs h hp (by omega); let C:= ((ηP A h).neg.mul P).mono (le_of_lt (show _<Deb by unfold Deb; norm_num)); have he:= (C.sub (hG.mono (show _≤ Deb by unfold Deb;norm_num)) (carth h)).sub (wagerE h hp) (carth h); apply he.congr; filter_upwards [flagFree A h x hp H,ηO A h,hymn A h] with i hi hx hM; change -(Bounty A i)*(_-_)-(_-_)-_= CoinΩ A i _-_; rw [goodness i (x i) hi, ← polH hs i (x i) hx.1 hM.1]; ring
end
end YM.OPE.Owl.HillZ
