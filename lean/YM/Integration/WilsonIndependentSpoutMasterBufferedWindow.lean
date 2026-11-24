import YM.Integration.WilsonIndependentSpoutMasterBufferedClock
import YM.Integration.WilsonPositionProgramTrialHomeFaces

/-! A single UV buffer pays the reporting-clock change for all fitted measurements on the original finite portfolio. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterBufferedWindow
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace (Initialize)
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonIndependentSpoutMasterUpperClocks (Paid)
open WilsonIndependentSpoutMasterCutoff (Earned rent)
open WilsonIndependentSpoutMasterReport (report)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialStationHome (chargeAt mass)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonIndependentMatchedFiledIncome (charge)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n e k u₀ u:ℕ}
local notation "I" => Fin (n+1)
local notation "credit" => Credit.leanC

def budget (W C:Credit)(a Z:ℝ)(B cap:I→ℝ):ℝ:=
    |C.buy Z| *∏i,|B i| *(|W.buy a| *cap i)

theorem fits (Q:I→SealR G)(C W:Credit)(clock:ℕ→ℝ)(m:ℕ)(b:Herit Q)(e:ℕ)(Z:ℝ)(B cap:I→ℝ)
    (earned:∀i,fee b e i ≤ cap i):|rent C W clock Q b e m Z B| ≤ budget W C (clock m) Z B cap:=by
  have positive i:0 ≤ fee b e i:=by unfold fee; positivity
  simp only [rent,budget,abs_mul,Finset.abs_prod,abs_of_nonneg (positive _)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.prod_le_prod (fun i _=>mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (positive i)))
  intro i _
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (earned i) (abs_nonneg _)) (abs_nonneg _)

variable (R:Run G)(l d:Fin (n+1)→ℕ)(admit:∀i,l i<d i)
local notation "Q₀" => deck (G:=G) l d admit
local notation "L₀" => R.family.path.levels

theorem paid {j:ℕ}{C W D:Credit}(sale:Earned R l d admit j e u C W)(income:Paid R j e D)
    (v m K:ℕ)(B cap:I→ℝ)(Z:ℝ)(awake:j ≤ v)(early:v ≤ m)(pre:m ≤ K)
    (optic:Compar (L₀).S (zz L₀) v m ≤ Z)(q:ℕ)(hq:q ≤ e)(ε:ℝ)(pos:0<ε):
    ∀ᶠ U:ℕ in atTop,K ≤ U ∧ ∀(N M:ℕ)(b:Herit Q₀)(F:Wilt Q₀)(y:ℝ)(o:CellR),
      U ≤ N → U ≤ M → (∀i,fee b e i ≤ cap i) → Bough Q₀ F y Z B → ∀g:ℝ,|g|≤1 →
      let Y:=ground (stopped L₀ R.metals.O Q₀ F b m K M v y o)
      ‖cash q g (embed (report L₀ R.metals.O N m v Y - report L₀ R.metals.O M m v Y))‖ ≤ ε:=by
  let rate:=∑s∈range (q+1),((s+1:ℕ):ℝ)*(2*D.buy (Compar (L₀).S (zz L₀) v m))
  let total:=|rate| *budget W C (zz L₀ m) Z B cap
  have vanish:Tendsto (fun U=>total*trailC (L₀).S m U) atTop (𝓝 (total*0)):=
    tendsto_const_nhds.mul (WilsonCoeffUV.Bank.PathCost.fade (L₀).S m)
  rw [mul_zero] at vanish
  filter_upwards [eventually_ge_atTop K,vanish.eventually (Iio_mem_nhds pos)] with U late small
  refine ⟨late,?_⟩
  intro N M b F y o live twin salaries fit g chip
  have onClock:=WilsonIndependentSpoutMasterBufferedClock.original R l d admit sale income v m K U N M b F B Z y o
    awake early pre late live twin optic fit q hq g chip
  let A:=rent C W (zz L₀) Q₀ b e m Z B
  have cost:rate*A ≤ total:=by
    apply (le_abs_self _).trans
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (fits Q₀ C W (zz L₀) m b e Z B cap salaries) (abs_nonneg _)
  apply (le_trans _ (le_of_lt small))
  apply le_trans _ (mul_le_mul_of_nonneg_right cost (trail_pos (L₀).S m U).le)
  simpa only [rate,A,Finset.sum_mul,mul_assoc] using onClock

theorem filed (W:Initialize G)(own:∀i,Rails (l i) k u₀ e)(kind:I→Bool)
    (c:∀i,Verse (R.family.labels.level (l i)))(α:∀i,Alma (R.family.labels.level (l i))→ℝ)
    (Z B:I→Credit)(m K N:ℕ)
    (X:∀i,CutsP (hol G) (Q₀ i).ans (Q₀ i).path (own i) credit credit credit credit)
    (filing:Filed R W l d admit kind own c α Z B m K N X)(wage:I→ℝ)(price:∀i,charge e (c i) (α i) ≤ wage i):
    ∀i,fee (fun s=>home (Q₀ s) (X s)) e i ≤ |chargeAt L₀ (Q₀ i) e (B i) (Z i) m K| *wage i:=by
  intro i
  exact ((filing i).2.2).trans (mul_le_mul_of_nonneg_left (price i) (abs_nonneg _))
end YM.Integration.WilsonIndependentSpoutMasterBufferedWindow
end
