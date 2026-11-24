import YM.Integration.FVA1Physical.Sources.Round2.FieldProjection
import YM.MSbar.Mosaic.Oracle

/-! Uniform normalized mixed field comparison along a family of paid Wilson scenes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open YM.MSbar YM.MSbar.Mosaic YM.MSbar.Mosaic.Issue YM.Integration.FVA1Physical.Wilson
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
variable {κ : Type} [Fintype κ] (lamps : κ→Lamp G) (part:Bool) (placement:ℕ)

include hcut

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 5000 in
/-- Under precisely the stage grants used to purchase the vacuum comparison,
the normalized conditional Haar field compares to the independently computed
mixed Wilson column. The constant is uniform in all source placements in the
growing collar and all exterior configurations in the regular portal. -/
theorem offer_fields : ∃ E:ι→ℝ, Mosaic.Run φ Y E (epsW p) ∧ ∀ᶠ i in φ,
    ∀ o:κ→Site (A i).f, (∀ l:Slice lamps,separation (z i) (legs lamps o l).1 ≤ placement*closeN (Y i)) →
    ∀ U∈(A i).regionX (Y i) (z i) (W i) J P,
    |(A i).modelP (Y i) (z i) (W i) P J (fun v=>look part (Spool.tally lamps o v)) U -
      taste p (innerColumn (A i) χ J (Y i) ((A i).fClock•W i) (z i) U (jointFieldBank lamps (A i) o part) p)
        (A i).fClock| ≤ E i := by
  let y:=Y
  have rise:Tendsto y φ atTop:=(Work.E09.betaF_growth G K.L).comp hX
  obtain ⟨_,a,ar,act⟩:=Mosaic.Issue.hammer hX χ J H H' K D hG hχ hp hq M i' hc h₁ ha hk hT
  have a0 : ∀ᶠ i in φ,0 ≤ a i := act.mono fun i hi=>(hi p le_rfl).2.1.1
  have step : 1 ≤ k:=by omega
  let B:=stencilSalary lamps p k placement part step
  have B0 : 0 ≤ B:=zero_le_one.trans (stencilSalary_pos lamps p k placement part step)
  obtain ⟨O,salary,E,E',_,stamp,ready⟩:=Mosaic.Issue.portion hX χ J H H' K D hG hQ hχ hp hq W hW M i' hc z hR P B h₁ ha hk hT hμ hb hb' hK B0 ar a0
  let radius i:=3*shade G*rot P (y i)
  let field i:=fieldCost lamps part p*(radius i)^(p+1)
  have rr : Mosaic.Run φ y radius (-(1/2):ℝ):=(Mosaic.height rise P J).2.2.2.1.mulK rise _
  have fieldRate : Mosaic.Run φ y field (epsW p):=(Mosaic.Run.tr rise rr).mulK rise _
  have small : ∀ᶠ i in φ, radius i ≤ fieldRadius lamps part p :=
    (rr.bouquet rise (by norm_num)).eventually (ge_mem_nhds (fieldRadius_pos lamps part p))
  refine ⟨fun i=>field i + Salary.stamp (salary i) p (N' i) (t' i) (E i) (E' i),fieldRate.addR rise stamp,?_⟩
  have high : ∀ᶠ i in φ, 1≤hatW (y i) := (Alto.broad.comp rise).eventually_ge_atTop 1
  have wide : ∀ᶠ i in φ, 2*placement≤radiusB (y i) :=
    rise.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (2*placement))
  have clocks : ∀ᶠ i in φ,(A i).fClock≤1 :=
    (Mosaic.Issue.shapeK (A:=A) hX J H H' K hG hp W hW).mono fun i hi=>hi.2.2.1
  filter_upwards [hp,hK,hc,hcut,ready,act,small,high,wide,clocks] with i paid geometry staff cut proj act good hi distance clock
  intro o near U inside
  have cover (l:Slice lamps): 2*separation (z i) (legs lamps o l).1 ≤ spotN (y i) :=by
    apply (Nat.mul_le_mul_left 2 (near l)).trans
    unfold closeN spotN;rw [pow_succ' (radiusB (y i)) 3,←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ distance
  have goodCut : Lodge.Hat k (O i).w (g i) (cutoff i):=proj.vlog.symm ▸ cut
  exact projection_field lamps (A i) χ J P K H H' p k placement step (W i) (z i) (O i) (salary i)
    (cutoff i) part o paid.space.symm paid.payments hQ staff.1 hχ geometry.spot geometry.price clock
    goodCut hi (fun j hj=>(act j hj).2) proj near (wires_inside lamps (A i).S (A i).F o (y i) (z i) cover) good U inside

end YM.Integration.FVA1Physical.Round2.Curvature
