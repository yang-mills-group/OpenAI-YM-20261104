import YM.MergeProof.South.Block
import YM.Integration.LocalComparisonInterface

/-! Terminal payment for a complete reflected product on a carrier with the
original quiet density. The signed marked density uses the carrier's own hard
addresses. All cell moments retain one common Wilson partition function. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReplicaTerminalCarrier

open Finset MeasureTheory Function Lattice Wilson RG Push Marker Source Extra.Histories
open MergeProof MergeProof.Accent Extra.Multi Cells LocalComparison Overlay
open scoped Topology BigOperators Classical

variable {G : Gauge} (C : Family G) (H : C.Makes) {N p u J : ℕ}
variable (ju : J≤u) (live : u≤N)
local notation "V" => Site (C.side J p)
local notation "T" => center C.S p (ju.trans live) 0
local notation "A" => C.path.levels
local notation "Q" => C.path.levels.clock

/-- The top census uses the original reflected child positions, conjugations
and the entire signed function at every cell. -/
def opening (F : Config G (C.side N p)→ℂ) :=
  birth (Stock.census V) (C.path.rep N p N) (fun i => (T).copy i F)

def arrival (F : Config G (C.side N p)→ℂ) :=
  gust C.path N p N (opening C ju live F) u live

include H in
theorem integral (F : Config G (C.side N p)→ℂ)
    (hi : Integrable (opening C ju live F) (prior G (C.side N p)))
    (hf : Integrable (fun U=>∏ i : V,(T).copy i F U) (law G (C.side N p) (C.beta N p))) :
    (∫ U,((arrival C ju live F) U).part (Stock.final V) ∂prior G (C.side u p)) =
      (Wilson.partition G (C.side N p) (C.beta N p):ℂ)*moment (C.beta N p) (fun U=>∏ i : V,(T).copy i F U) := by
  let L := (Poly.get (Stock.final V)).restrictScalars ℝ
  have marg := gust_sum C.path N p N (opening C ju live F) hi live
  have hj := gust_live C.path N p N (opening C ju live F) hi live
  calc
    _ = L (∫ U,arrival C ju live F U ∂prior G (C.side u p)) := L.integral_comp_comm hj
    _ = L (∫ U,opening C ju live F U ∂prior G (C.side N p)) := congr_arg L marg
    _ = ∫ U,(opening C ju live F U).part (Stock.final V) ∂prior G (C.side N p) := (L.integral_comp_comm hi).symm
    _ = _ := by
      rw [moment_formula _ _ hf,mul_inv_cancel_left₀ _ (_:ℂ)]
      · simp_rw [opening,birth,(H.wilson.starts N p).2,Poly.part_smul,Mach,Extra.Trajectories.pass_fire]
        rfl
      exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'

include H in
theorem original (F : Config G (C.side N p)→ℂ)
    (hi : Integrable (opening C ju live F) (prior G (C.side N p)))
    (hf : Integrable (fun U=>∏ i : V,(T).copy i F U) (law G (C.side N p) (C.beta N p)))
    (P : Carrier C N p u) (beta : P.rep.beta=(C.path.rep N p u).beta)
    (admitted : P.rep.Lawful ((A).params u).width ((A).params u).paths ((Q).loopCap u)
      ((Q).allowance u) ((Q).forcedAllowance u))
    (F₀ : V → Config G (C.side u p)→ℂ) (F₁ : V → Box (C.side u p) → Config G (C.side u p)→ℂ)
    (o : V→Site (C.side u p)) {w x y f : ℝ} (hw : 0<w)
    (served : Served P.rep F₀ F₁ (arrival C ju live F) o (fun _=>w) ((A).budget u).supportExponent f)
    (vault : Vault (fun _:V=>w) F₀ F₁ x y) :
    (T).rootTest (C.beta N p) F ≤ Real.exp ((C.S.a J/C.S.a u)^4*Vac.treasury A u+x+y+2*f)/w := by
  let Z:=Fintype.card V
  let d:=(C.S.a J/C.S.a u)^4*Vac.treasury A u+x+y+2*f
  have rep := H.wilson.represents N p u live
  have pos : 0<(Q).hatCoupling u := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ((A).fits.delayed u)))
  have ht : (Q).hatCoupling u≤P.rep.p.threshold :=by
    rw [P.point]; exact le_mul_of_one_le_right pos.le (Real.one_le_exp (sq_nonneg _))
  have hb : 0≤P.rep.beta := beta.symm ▸ (Overlay.beta_positive H.wilson live).le
  have hg (U) : 0≤P.rep.eval U := by rw [P.vacuum]; exact History.nonnegative C.path H.wilson N p u live U
  have bill := sail (r:=fun _:V=>w) (fun _=>hw) served admitted hb vault ((A).budget u).exponent_pos.le
    (Stock.final V) (gust_live C.path N p N _ hi live) _ pos ht hg
  have same : P.rep.p=(C.path.rep N p u).p := P.point.trans rep.vac.symm
  rw [Bands.finalBill,Rep.exCost,same,beta,P.clip] at bill
  have cap := (Vac.suffices_bill (p:=p) H.wilson live Z x y (2*f) 1)
  change Bands.finalBill Z (C.path.rep N p u) _ x y (2*f) 1 _ _ _ _ ≤ _ at cap
  rw [Bands.finalBill,Rep.exCost] at cap
  have amount := bill.trans (Real.exp_monotone cap)
  rw [integral C H ju live F hi hf,P.vacuum,History.partition_eq C.path H.wilson N p u live,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le,mul_comm (Wilson.partition ..),
    mul_div_cancel_right₀ _ (partition_pos _).ne'] at amount
  unfold Tiling.rootTest
  apply Stock.spacer _ d w Z (norm_nonneg _) hw Fintype.card_pos
  have wage : Poly.toll (R:=Stock.census V) (fun _=>w) (Stock.final V)=w^Z := by simp [Poly.toll,Stock.final,Z]
  rw [wage] at amount
  apply amount.trans_eq
  congr 1
  rw [Stock.tallies C.S J u p]
  unfold Z d
  ring

end YM.Integration.WilsonReplicaTerminalCarrier
