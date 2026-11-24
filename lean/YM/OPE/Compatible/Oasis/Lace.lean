import YM.OPE.Compatible.Oasis.Drape
import YM.OPE.Compatible.Oasis.Quark
import YM.OPE.Compatible.Oasis.Pure
import YM.OPE.Compatible.Kyoto.Orbs
import YM.OPE.Compatible.Oasis.Ball
import YM.OPE.Compatible.Kyoto.Ploy
import YM.OPE.Compatible.Kyoto.Team
import YM.OPE.Compatible.Kyoto.Cloud
import YM.OPE.Compatible.Kyoto.Gazer
import YM.OPE.Compatible.Kyoto.Opal
import YM.OPE.Compatible.Kyoto.TreeQ
import YM.OPE.Compatible.Ice.Ares
import YM.OPE.Compatible.Nut.Hero
import YM.OPE.Compatible.Silva.Bride
import YM.OPE.Compatible.Kyoto.Room
/-!
# Uniform transport bounds above a coarse-period threshold

`Whit` combines the period threshold from `RequestZ` with the lower
bound for the reciprocal-period estimate. For all sufficiently large
times `x`, `Concur` gives `PacketE` for every matched step meeting
that threshold and admitting `Aud`, and for every associated `HerdW`.
The common norm bound is `ages b x` for `b > 0`. The operator discrepancy
is at most `ages tuneJ x`, with `tuneJ = -107/100`.
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
variable {n c f:Side}{I J :Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{C:KernelChoices}{p p':Clip}
variable {v v' b u:ℝ}{U:Boxes G P K.K}

variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full GlowPack Yolk Pipes Dial Raucous Zeph Zeph.Dew Borealis Flume.Script 
open Next.Free
section
variable {L:PriceBook H T}{a:Axis}
namespace MatchZ

section
open Lass.Zest Lass PhysicalNext.Repeat.Aroma Pressure ConnectedActivityE6 Shell Channel
variable {Ξ:Medal P' G K.K P'.J} {P₀:Teller G}
variable {E:ConnectedActivityE6.Target G P₀} {Q:Side}{W C κ:ℝ}{o:ConnectedActivityE6.Target.Order G W}
variable (F:I→Mug P' p p' T j R Ξ)
variable {Q:ℕ}
open Limn CardinalQ Labels Source Cameo Spells Yolk Pill
open Next.Scheduling
variable {X₀:Uniform G P'}
variable (N:Foyer L hs a l (d+6)){hp:highStage L hs a N≤ P'.J}{hz:highStage L hs a N ≤ j}
variable {M:Cab T j p}{β:I→ℝ}{l₀:Filter I}
variable {T1 T2:RG.Stage}(W:∀ i, Pillar X₀ (F i) (β i)) (h:Tendsto β l₀ atTop) (hc:∀ i,Aud X₀ (F i) T1 T2 (β i) (W i))
local notation "ζ"=> Eve W
local notation "Γ"=>βM ζ
variable (hZ:Mag P'.J j)(hb:P'.L=N.pay.st.S.L^m)
variable (Y₀:BankW L hs a N hp p)(C₀:BankW L hs a N hz p')

section
variable {A:Labels.Frame G l}{S:SectionData A}{U₀:Hol G}(P0:Spells.Pad G)
-- The period threshold below uses firstΖ and tuneE. The final error estimate uses tuneJ.
abbrev firstΖ := -(109/100:ℝ)
abbrev tuneE := -(108/100:ℝ)
abbrev tuneJ := -(107/100:ℝ)
abbrev Whit (YY:Patch)(V:Foyer L hs a l (d+6))(hz:4 ≤ j)(hr:l+6 ≤d)(x:ℝ):ℕ:= RequestZ (P':=YY) (j:=j) V hz hr firstΖ tuneE (by norm_num [firstΖ,tuneE]) (by norm_num [firstΖ]) ℕ (Real.log (now x G YY))+ Nat.ceil (Real.exp (-(firstΖ*Real.log (now x G YY))))
structure HerdW (x:ℝ)(M:Mug P' p p' T j R Ξ)(S:SectionData A)(U₀:Hol G) (T1 T2: Stage) (d:ℕ)(C:ℝ) where
       Pfe :A.Coeff → Coefficient A M.f
       Pco : A.Coeff → Coefficient A M.c
       escort: Torch S U₀ 0 M.pW Pfe d (salary (now x G P'))
       shield: Torch S U₀ 0 M.pV Pco d (salary x)
       Kcap: Grant (z:=now x G P') escort T1
       Scap: Grant (z:=x) shield T2
       Mat: A.Coeff→L[ℂ] A.Coeff
       bounded: ‖Mat‖≤ C
       matchP:∀ v:A.Coeff,(Pco (Mat v)).density 0 S M.pV= ((P'.L.val:ℝ)^l) • (M.hostS.Z.push M.pW.beta ((Pfe v).density 0 S M.pW))
variable {C':ℝ} 
abbrev PacketE (x:ℝ)(M:Mug P' p p' T j R Ξ)(H:HerdW x M S U₀ T1 T2 d C') :Prop := PrimC N Y₀ C₀ x (ages b x) M ∧ ‖(ClockVal N C₀ M.row.coarse S P0 H.shield (Clock.gap M.pV.beta)).comp H.Mat-(Adventure N Y₀ C₀ P'.L (Stint N M.row Ξ) M.row.fine M.row.coarse (Clock.gap M.pW.beta)).comp (ClockVal N Y₀ M.row.fine S P0 H.escort (Clock.gap M.pW.beta))‖≤ ages tuneJ x
variable (T1 T2:Stage) (X0:Uniform G P')(hD:l+6 ≤d) (b:ℝ) (he:0<b)

set_option maxRecDepth 4096
set_option maxHeartbeats 200000
variable (S U₀ C')
include hZ hb he
lemma Concur :∀ᶠ x:ℝ in atTop,∀ M:Mug P' p p' T j R Ξ, Whit P' N (hazard N hz) hD x ≤ M.c.val→ (∃ t:Pillar X0 M x,Aud X0 M T1 T2 x t)→ ∀ P:HerdW x M S U₀ T1 T2 d C', PacketE (b:=b) N Y₀ C₀ P0 x M P:=by
        by_contra h; rw [not_eventually] at h; simp only[Classical.not_forall, exists_prop] at h
        choose f hF M he' hWV using fun i:ℕ=> frequently_atTop.mp h (i:ℝ); choose V hV using fun i=> (hWV i).1; choose P hP using fun i=> (hWV i).2; have hz': Tendsto f atTop atTop:=tendsto_atTop_mono hF tendsto_natCast_atTop_atTop; have hh: Receipt f atTop (fun i=>(P i).Mat):= Score.bound _ (carth hz') (Eventually.of_forall fun i=>(P i).bounded);
        have hB:= ArcZ M N V hz' hV hZ hb Y₀ C₀ he;
        have hp(i:ℕ): RequestZ (P':=P') (j:=j) N (hazard N hz) hD firstΖ tuneE (by norm_num [firstΖ,tuneE]) (by norm_num [firstΖ]) ℕ (Real.log (now (f i) G P')) ≤ (M i).c.val:=Nat.le_of_lt_succ (Nat.lt_succ_of_le ((Nat.le_add_right _ _).trans (he' i)))
        have hx(i:ℕ): Real.exp (-(firstΖ*Real.log (now (f i) G P'))) ≤ (M i).c.val:=(Nat.le_ceil _).trans (Nat.cast_le.mpr ((Nat.le_add_left _ _).trans (he' i)))
        have hΩ:= StaveK M N V hz' hV hZ hb Y₀ C₀ (fun i=>(P i).escort) (fun i=>(P i).shield) (fun i=>(P i).Kcap) (fun i=>(P i).Scap) P0 _ hh (fun i=>(P i).matchP) hD (by norm_num [firstΖ]:-(11/10:ℝ)< firstΖ) (by norm_num [firstΖ,tuneE]:firstΖ< tuneE) hp hx; obtain ⟨i,h',hR⟩:= (hB.and (hΩ tuneJ (by norm_num [tuneJ,tuneE]))).exists; exact hP _ ⟨h',hR⟩
end
end
end MatchZ
end
end YM.OPE.Stroke
