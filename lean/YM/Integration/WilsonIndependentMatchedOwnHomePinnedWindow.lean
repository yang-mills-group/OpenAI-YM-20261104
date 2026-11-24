import YM.Integration.WilsonIndependentMatchedOwnHomePinnedRoster
import YM.Integration.WilsonIndependentSpoutMasterReportedBasis

/-! The paid fixed-order cutoff sector at an actual located lattice pin. The
aperture depends on the optical homes and the outer field and precedes K. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomePinnedWindow
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedCoverProfile (word)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedOwnHomePinnedPlacement (moved)
open WilsonIndependentMatchedOwnHomePinnedMaster (point)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonSeparatedPrefixMovingPinHearing (hear shiftHom)
open WilsonPositionProgramPinnedHearthHistory (pin)
variable {G:Gauge}{n e:ℕ}{E:Credit}

open WilsonIndependentMatchedOwnHomePinnedRoster (translated)
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Power WilsonCoeffUV.Mer.Patrol
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentSpoutMasterReportedBasis (price)
open WilsonIndependentSpoutMasterCutoff (Earned)
open WilsonIndependentSpoutMasterClockFees (Paid)
open WilsonIndependentSpoutMasterBasisCutoff (bank)
open WilsonIndependentSpoutMasterReport (report)
variable {D h l:ℕ}

def size (S:Schedule)(Φ:Rarity D)(m t c:ℕ)(y:ℝ):ℝ:=
    paceT S m t*(radiusH Φ (paceT S t c) y+1)

theorem extent (S:Schedule)(Φ:Rarity D)(m t c:ℕ)(y:ℝ)(s:Cover)(inside:s∈canvasM Φ (paceT S t c) y)(chron:t ≤ c):
    ‖paceT S m c • actualW s‖ ≤ size S Φ m t c y:=by
  let ε:=paceT S t c
  let Δ:=paceT S m t
  let R:=radiusH Φ ε y
  let k:=cairnM Φ ε y
  have pos:0<ε:=pace_pos ..
  have Tpos:0<Δ:=pace_pos ..
  have rk:0 ≤ R:=zero_le_one.trans (fieldCap ..)
  have sites:‖actualW s‖ ≤ (k:ℝ):=by
    apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr;intro i
    have hj:=Finset.mem_Icc.mp (Fintype.mem_piFinset.mp inside i)
    change ‖((s i:ℤ):ℝ)‖ ≤ _
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · exact_mod_cast hj.1
    · exact_mod_cast hj.2
  have rule:paceT S m c=Δ*ε:=by
    dsimp only [Δ,ε,paceT];field_simp [(S.a_pos _).ne']
  have ceil:(k:ℝ) ≤ R/ε+1:=by
    dsimp only [k,cairnM];rw [abs_of_pos pos];exact (Nat.ceil_lt_add_one (div_nonneg rk pos.le)).le
  rw [norm_smul,Real.norm_of_nonneg (pace_pos ..).le,rule]
  calc
    _≤(Δ*ε)*(R/ε+1):=mul_le_mul_of_nonneg_left (sites.trans ceil) (mul_nonneg Tpos.le pos.le)
    _=Δ*(R+ε):=by field_simp [pos.ne']
    _≤_:=mul_le_mul_of_nonneg_left (add_le_add_right (pace_le S chron) _) Tpos.le

variable (P:Run G)(L d:Fin (n+1)→ℕ)(admit:∀i,L i<d i)
local notation "Q₀" => deck (G:=G) L d admit
local notation "A₀" => P.family.path.levels
local notation "O₀" => P.metals.O

theorem original {anchor low mem:ℕ}{main basis clock:Credit}
    (sale:Earned P L d admit anchor low mem main basis)(fees:Paid P anchor low clock)
    (R:Realm G (e+1) E)(levels:R.draws=A₀)(vac:R.paid=O₀)
    (m t c old K N:ℕ)(openAt:anchor ≤ old)(ear:old ≤ m)(cut:m ≤ K)(top:K ≤ N)(onset:t ≤ c)(enrolled:c ≤ K)
    (a:∀i,Alma (Q₀ i).F)(φ:Wilt Q₀)(Φ:Rarity D)(y z:ℝ)(o:CellR)(s:Cover)(inside:s∈canvasM Φ (paceT (A₀).S t c) z)
    (room:ℝ)(B:Fin (n+1)→ℝ)(optic:Compar (A₀).S (zz A₀) old m ≤ room)(bough:Bough Q₀ φ y room B)(j:ℕ)(hj:j ≤ low):
    let Z:=room+size (A₀).S Φ m t c z
    twain (price P main basis clock old m j Z B) (trailC (A₀).S m K)
      (PowerSeries.coeff j (report R.draws R.paid N m old (point R Q₀ φ (bank Q₀ a) m c old K N y o s)))
      (PowerSeries.coeff j (report R.draws R.paid K m old (point R Q₀ φ (bank Q₀ a) m c old K K y o s))):=by
  intro Z
  let v:=paceT (A₀).S m c • actualW s
  have bound:‖v‖ ≤ size (A₀).S Φ m t c z:=extent (A₀).S Φ m t c z s inside onset
  have bigger:room ≤ Z:=le_add_of_nonneg_right ((norm_nonneg _).trans bound)
  have grant:=WilsonIndependentMatchedOwnHomePinnedRoster.bough Q₀ φ v room y B bough
  have admitted:Bough Q₀ (translated Q₀ φ v) y Z B:=boughRise grant (add_le_add_right bound _)
  rw [WilsonIndependentMatchedOwnHomePinnedRoster.original R Q₀ φ _ m c old K N enrolled ear cut,
      WilsonIndependentMatchedOwnHomePinnedRoster.original R Q₀ φ _ m c old K K enrolled ear cut,levels,vac]
  exact WilsonIndependentSpoutMasterReportedBasis.original P L d admit sale fees old m K N a _ B Z y o openAt ear cut top (optic.trans bigger) admitted j hj

end YM.Integration.WilsonIndependentMatchedOwnHomePinnedWindow
end
