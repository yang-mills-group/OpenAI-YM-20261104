import YM.Integration.FVA1Physical.Wilson.PacketProjection
import YM.MSbar.Mosaic.Oracle

/-! Every normalized distributed packet and every regular portal field share
the same inherited-action and covariance receipt before choosing the torus. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open YM.MSbar YM.MSbar.Mosaic YM.MSbar.Mosaic.Issue YM.Integration.FVA1Physical.Wilson
open YM.Integration.FVA1Physical.Round2.Curvature (clockReading)
open RGComparison.Core16 RGComparison.Core16.Spool

open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior YM.Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
variable {ι:Type}{X f' g H0:ι→ℝ}{A:ι→Issue G}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop) (χ:ChartRatio G)(J:Voice G)(H H':Stage)(K:Patch)(D:KernelChoices)
variable (hG:G.Simple) (hD:K.Branches D G)(hQ: Clear G J)(hχ:LocalRatio χ)
local notation "α'" i=> tip G K.L (X i)
local notation "Y"=> fun i:ι=> tip G K.L (X i)
local notation "w'" i=> vol (tip G K.L (X i))
local notation "t'" i=> (A i).fClock
variable (hp:∀ᶠ i in φ,Paid (A i) K H H' J (X i)) (hq:∀ᶠ i in φ,(A i).S.kernel=D)
variable (W:(i:ι)→Positions (Primary (A i).c G))(hW:∀ᶠ i in φ,‖W i‖ ≤ hull (X i))
variable {p m k q L:ℕ}
variable (M:StageCost)(i':G.ColorIndex){s' e ν b:ℝ}(hc:∀ᶠ i in φ,Festival (A i) χ p i' ∧ ClockD (A i) p m M.s (X i)∧ Cs (A i) χ M.s p m (X i) i' (f' i) b ∧ Issue.Receipt (A i) M (X i))
variable (z:(i:ι)→Site (A i).f)
variable (hR:∀ᶠ i in φ,Ore M (X i) K)
variable (P:Palisade){τ b':ℝ}(B :ℝ)
local notation "x'" i=> boxX (tip G K.L (X i)) (z i)
local notation "x₁" i=> boxY (tip G K.L (X i)) (z i)
local notation "N"=> k*(p+2)
local notation "N'" i=> Fintype.card (Lake (A i).F (boxX (α' i) (z i)) G)
local notation "N₁" i=> (keepB (A i).F (x' i) G).card
local notation "N₂" i=> (keepF (A i).F (x' i)).card
local notation "Γ" i=> Ruby.crownP (A i).F (A i).M (W i)
local notation "Φ'" i=> inkW (N₂ i)
variable (h₁:p+2≤ m)(ha:Mosaic.Run φ X f' 0)(hk:k=m+1)(hT:p+3≤ k)(hμ:4 ≤ m)(hb:0<τ)(hb':0≤b')
local notation "γ" i=> thorn (Y i) (k*(p+2))
variable (hK:∀ᶠ i in φ, Issue.Buy (A i) (W i) (boxX (tip G K.L (X i)) (z i)) (boxY (tip G K.L (X i)) (z i)) J P χ (tip G K.L (X i)) e s' (thorn (tip G K.L (X i)) (k*(p+2))) τ b')
include hX hp hc hR hW hχ hG hQ h₁ ha hk hT hμ hb hb' hq hK
variable (cutoff:(i:ι)→ℝ→ℝ) (hcut:∀ᶠ (i:ι) in φ,Lodge.Hat k (vol (tip G K.L (X i))) (g i) (cutoff i))

include hcut

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4500 in
theorem offer_packets (degree:ℕ) (enough:degree ≤ k*(p+2)) :
    ∃ E:ι→ℝ,Mosaic.Run φ Y E (epsW p) ∧ ∀ᶠ i in φ,
      ∀ (copied:Bool) (T:Nesting G (A i).f),BankPaid (z i) (Y i) 0 p degree 0 T →
      (PowerSeries.coeff 0 T).totalDegree=0 → ∀ U∈(A i).regionX (Y i) (z i) (W i) J P,
      |(A i).modelP (Y i) (z i) (W i) P J (fun v=>clockReading p (t' i) T (chartLog (t' i) (packetConfig (A i) J (Y i) (z i) (W i) copied v))) U -
        taste p (innerColumn (A i) χ J (Y i) ((t' i)•W i) (z i) U (enterRows (A i) T) p) (t' i)| ≤ E i := by
  let y:=Y
  have rise:Tendsto y φ atTop:=(Work.E09.betaF_growth G K.L).comp hX
  obtain ⟨_,a,ar,act⟩:=Mosaic.Issue.hammer hX χ J H H' K D hG hχ hp hq M i' hc h₁ ha hk hT
  have a0:∀ᶠ i in φ,0 ≤ a i:=act.mono fun i hi=>(hi p le_rfl).2.1.1
  have step:1 ≤ k:=by omega
  have paid0 : 0 ≤ packetSalary G p k:=zero_le_one.trans (le_max_left ..)
  obtain ⟨O,salary,E,E',_,stamp,ready⟩:=Mosaic.Issue.portion hX χ J H H' K D hG hQ hχ hp hq W hW M i' hc z hR P (packetSalary G p k) h₁ ha hk hT hμ hb hb' hK paid0 ar a0
  have small:=Mosaic.Run.core rise (epsW p)
  refine ⟨fun i=>(y i)^(epsW p)+Salary.stamp (salary i) p (N' i) (t' i) (E i) (E' i),small.addR rise stamp,?_⟩
  have apply_packets:=hX.eventually (packet_projection χ hχ J hQ P K H H' degree p k step (epsW p))
  filter_upwards [hp,hK,hc,hcut,ready,act,apply_packets] with i paid geometry staff cut proj action runner
  intro copied T bank flat U inside
  have goodCut:Lodge.Hat k (O i).w (g i) (cutoff i):=proj.vlog.symm ▸ cut
  exact runner (A i) (z i) T (W i) copied (O i) (salary i) (cutoff i) paid.space.symm paid.payments staff.1
    geometry.spot geometry.price goodCut enough (fun j hj=>(action j hj).2) proj bank flat U inside

end YM.Integration.FVA1Physical.Wilson
