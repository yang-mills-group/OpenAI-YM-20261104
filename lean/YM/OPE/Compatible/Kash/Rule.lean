import YM.OPE.Compatible.Kash.Pond
import YM.OPE.Compatible.Kash.Snow
import YM.OPE.Compatible.Ice.Room
import YM.OPE.Compatible.Chest.Booth
/-!
# Reading a field after subtracting a comparison in `SailSap`

`CropFill` supplies a controlled comparison field eventually in `Variance.SailSap`
and an `Audible` bound for its difference from `portrait`. When `β` tends to infinity
and the periods eventually meet `SiteEra`, `star_C` bounds the chosen real-linear
reading at exponent `q2`. `EraQ` combines the real and imaginary readings for `ClockVal`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "μ"=>lapPrice (Patch.L P)
section
open GlowPack Silt.Phere Ibis Owl Lass.Zest Spells Yolk Pill Dial
variable {L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i':ℕ)(he:highStage L hs a V ≤ i')
variable (S:Stage)(X:BankW L hs a V he S.clip) (P:Pad G)
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
local notation "F*"=> solar G (l+6+6) V.pay.st.τ
-- The family is indexed by the scale and lattice period.
variable {n:I→Side}{φ:Filter I}{β:I→ℝ} (ξ:ℝ)(r l':ℕ)
variable (A:∀ i, HillZ (T:=T) S i' r l ξ (β i) (n i))
local notation "Kι"=> hazard V he
open Next.Scheduling
local notation "PL"=> fun i:I=> (A i).lens
noncomputable abbrev εM (i):=Clock.gap (A i).path.beta
variable (g:ℂ→L[ℝ]ℝ) {ξ r}
noncomputable abbrev portrait (Q:HillZ (T:=T) S i' r l ξ b c)(g:ℂ→L[ℝ]ℝ):= tintX V (he:=he) Q.living Q.lens P (Clock.gap Q.path.beta) g Q.art
local notation "bι"=>fun i:I=>Clock.gap (A i).path.beta
structure CropFill :Prop where
       fills :∃ f:I→ solar G (l+6+6) (V.pay.st.τ),Alive φ (Counters β) f∧(∀ᶠ j in φ,f j∈ Variance.SailSap (A j|>.lens.ℳ) H (hazard V he) hs (zero_le_one.trans ((A j).lens.positive)) V.pay.st.S a l) ∧ Audible G K.K n φ (Counters β) i' (l+6) (fun i=>(A i).lens.ℳ.gear) (hazard V he) (fun i=> Aview (portrait V i' he S P (A i) g - f i) 0 ((bι) i)) q1 
variable (ht:Tendsto β φ atTop)(hM:∀ᶠ i in φ, SiteEra V i' he I (Counters β i) ≤ (n i).val)
include ht
open CardinalQ
lemma torν: Lass.Zest.Torch.BondS (fun i=>(A i).living) β φ (bι):= ClockFee ht _ (Eventually.of_forall fun i=>(A i).gen.TagQ) (Eventually.of_forall fun i=>(A i).cents.2)
include hM
lemma star_C (h:CropFill V i' he S P A g (φ:=φ)): RateLE φ (Counters β) (fun i=> FaithV V X (A i).living (A i).lens P ((bι) i) (A i).art g) q2:=by
        obtain ⟨f,hf,hA,H'⟩:= h.fills; have hc:= torν i' S A ht; have hx:Receipt β φ (fun i=> (A i).art):= (Score.steady (2:ℝ) (carth ht)).under (Eventually.of_forall fun i=> (A i).norm); have hT: Alive φ (Counters β) (fun i=>portrait V i' he S P (A i) g):= hc.FineB _ hx _ (hazard V he) _ g V.pay.st.hτ 
        have hp:Wax β φ (fun i=> (A i).lens.fees) 0:= ((CoinS ht ξ).pays (carth ht)).congr (Eventually.of_forall fun i=> (A i).salaryF.symm); exact Feast V i' he S X (carth ht) (by rw [←neg_div]; exact (worthP hc.Lamp).pays (carth ht)) hp hT hM f hf hA H'
lemma EraQ (h:∀ g:ℂ→L[ℝ]ℝ,CropFill V i' he S P A g (φ:=φ)): RateLE φ (Counters β) (fun i=> (ClockVal V X (A i).lens (localSection G _) P (A i).living ((bι) i)) (A i).art) q2:=by
        let p(i:I):= Swing V X (A i).living (A i).lens P ((bι) i) (A i).art; have hp:RateLE φ (Counters β) p q2:=by
               let B:=CanA (dims V); intro κ hv; filter_upwards [star_C V i' he S X P A Complex.reCLM ht hM (h _) _ hv,star_C V i' he S X P A Complex.imCLM ht hM (h _) _ hv] with i h k; change ‖(_,( _:B))‖≤ _; rw[Prod.norm_def]; exact max_le h k
        exact (hp.linear (carth ht) (Garm (dims V)).toContinuousLinearEquiv.toContinuousLinearMap).congr (Eventually.of_forall fun i=> (LaidS ..).symm)
end
end YM.OPE.Stroke
