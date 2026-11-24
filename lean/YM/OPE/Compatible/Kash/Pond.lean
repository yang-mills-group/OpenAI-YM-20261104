import YM.OPE.Compatible.Kash.Snow
import YM.OPE.Compatible.Ice.Room
import YM.OPE.Compatible.Chest.Booth
/-!
# Removing a field in the kernel of the reading

`SaintL` and `islands` show that `Eout` and `τPledge` vanish on `Variance.SailSap`.
`Feast` uses this cancellation after subtracting a comparison field. Under its
field and clock bounds and the `SiteEra` period cutoff, an `Audible` estimate at
`q1 = -27/25` gives a `τPledge` estimate at `q2 = -26/25`.
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
open GlowPack
variable (W:GlowPack Hp Z a (k:=k)) (U:Z.Ω M Y)(hq:1 ≤ Y)(hp:4 ≤ i)(V:(i':M)→Alps K T i (Y i'))
local notation "W!"=>Dux G l W.W
local notation "E!"=>Eagle Hp Z a W
variable {W Hp Z a U V} {hq hp}
variable (D:Cart Hp Z a W U hq hp V) (j':M)
open GlowPack
open Silt.Phere
open Ibis
set_option maxHeartbeats 200000
lemma SaintL (p:solar G d τ)(he:p ∈ Variance.SailSap (V j') H hp hs (le_trans zero_le_one (hq _)) P a l) : Eout D j' p=0:=by
        let x:= Fallix G D₀.aware K (V j').gear hp; have ht: x.symm p∈ Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀) j':=by change x (x.symm p) ∈ Variance.SailSap (V j') H hp hs (zero_le_one.trans (hq _)) P a l; rw [x.apply_symm_apply]; exact he
        exact (Mercy (H:=D.F) D.fee W.fro j' (x.symm p)).1 (le_sup_right (a:=U.flag (l+1) j') ht)
lemma islands (p:solar G d τ)(s:ℝ)(he:p ∈ Variance.SailSap (V j') H hp hs (le_trans zero_le_one (hq _)) P a l):τPledge D j' s p=0:=by
        calc
          _ = FilmP E! s (Eout D j' p) := ζshot D j' s p
          _ = FilmP E! s 0 := congrArg (fun z => FilmP E! s z) (SaintL D j' p he)
          _ = 0 := map_zero _
lemma gapE (p q:solar G d τ)(s:ℝ)(he:p ∈ Variance.SailSap (V j') H hp hs (le_trans zero_le_one (hq _)) P a l):τPledge D j' s (q-p)= τPledge D j' s q:=cancel_k _ _ _ (islands D _ _ _ he)
where cancel_k {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F](M:E →L[ℝ] F)(x y:E)(h:M y=0): M (x-y)=M x:=by rw [map_sub,h,sub_zero]
end
section
open Ibis Owl Lass.Zest Spells Yolk
variable {L:PriceBook H T}{a:Axis}(V:Foyer L hs a l (l+6+6))(i':ℕ)(he:highStage L hs a V ≤ i')
-- Choose the period threshold for the fixed pair of rate exponents.
variable (S:Stage)(X:BankW L hs a V he S.clip)
set_option quotPrecheck false
local notation "Z"=> V.pay.st.τ
local notation "Y"=> V.pay.st.S
local notation "h*"=> V.pay.st.hτ
local notation "LW"=> Cab T i' S.clip
local notation "gT"=>Ibis.Hear 
noncomputable abbrev q1 :ℝ:= -(27/25) 
noncomputable abbrev q2 :ℝ:= -(26/25)
lemma qφ : q1<q2:=by unfold q1 q2; norm_num
noncomputable abbrev SiteEra (Ξ:Type) :ℝ→ℕ:= (Hear (I:=Ξ) G K.K (hazard V he) Z (l+6+6) h* qφ (show l+1+6 ≤ l+6+1 from by omega) (show (-(1/2):ℝ) ≤ 0 from by norm_num) (by unfold q1; norm_num)).choose
variable {F':I→Cab T i' S.clip}{p':I→solar G (l+6+6) V.pay.st.τ}{c w:I→ℝ}{B':I→Side}{o:∀ i,Site (B' i)}{φ:Filter I}
set_option maxHeartbeats 200000
lemma Feast (ht:Tendsto c φ atTop)(hv:RateLE φ c w (-(1/2)))(he':RateLE φ c (fun i=> (F' i).fees) 0)(hP:Alive φ c p')(hB:∀ᶠ i in φ, SiteEra V i' he I (c i) ≤ (B' i).val) (Y₀: I→solar G (l+6+6) V.pay.st.τ) (hY:Alive φ c Y₀)(hf: ∀ᶠ j in φ,Y₀ j∈ Variance.SailSap (F' j).ℳ H (hazard V he) hs (zero_le_one.trans (Yelite (F' j))) (V.pay.st.S) a l) (ha: Audible G K.K B' φ c i' (l+6) (fun i=> (F' i).ℳ.gear) (hazard V he) (fun i=> Aview (p' i - Y₀ i) (o i) (w i)) q1) : RateLE φ c (fun i=> τPledge X.cart (F' i) (w i) (p' i)) q2:=by
        let z:= X.cart; have hp':= AuroraWitness X.cart X.ear _ _ qφ (show l+6 ≤ l+6 from le_rfl) (show (-(1/2):ℝ) ≤ 0 from by norm_num) (by unfold q1;norm_num) (SiteEra V i' he I) rfl φ c w (p'-Y₀) B' o F' ht hB (hP.minus hY ht) hv he' ha
        refine hp'.congr (hf.mono fun i hi=>?_); change τPledge X.cart (F' i) (w i) (p' i-Y₀ i)=_; exact gapE X.cart _ _ _ _ hi
end
end YM.OPE.Stroke
