import YM.Integration.FVA1Physical.Sources.Round2.CurrentBoundary
import YM.Integration.FVA1Physical.Sources.Round2.PurchasedSignedBirth

/-! Push an actual mixed physical insertion through arbitrarily many uncut, normalized Haar laws. The exact native signed density at each boundary and its representation cost are retained through the complete history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MeasureTheory Lattice RG RG.Supply YM.Wilson Source Labels Precision Input Org Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open UVNext.CouplingReset Next.Foundations Graces Roost LocalLTE LocalLTE.Vinca LocalLTE.Concourse
open MergeProof Planned.GuardedAtom Planned.GuardedAtom.Guard Push Push.Local Push.AbsoluteSums
open RGComparison.Core16.Spool GapsR2RG GapsR2RG.Anchor MSbar MSbar.Bulk MSbar.Mosaic
open Tree MSbar.Midpoint
open YM.Integration.FVA1Physical.Wilson YM.Integration.FVA1Physical.Marked
open scoped Classical BigOperators Topology
variable {G:Gauge}

open YM.Integration.FVA1Physical.Round2.Curvature
open scoped BigOperators

variable (R:PhysicalNext.Repeat.Legato.Run G)
local notation "H" => R.family.path
local notation "F0" => (frames G).level 0
local notation "D0" => localSection G 0

def haarTape (N n u:ℕ) (φ:Config G (R.family.side u n) → ℝ) (j:ℕ) (hj:j ≤ u) :
    Config G (R.family.side j n) → ℝ :=
  Nat.decreasingInduction (motive:=fun i _=>Config G (R.family.side i n) → ℝ)
    (fun i _ next W=>expect ((H).levels.clock.op i n) ((H).rep N n (i+1)) W next) φ hj

def anchorTape (n u:ℕ) (b:Site (R.family.side u n)) (j:ℕ) (hj:j ≤ u) : Site (R.family.side j n) :=
  Nat.decreasingInduction (motive:=fun i _=>Site (R.family.side i n))
    (fun i _ w=>((H).levels.clock.op i n).ratio.parent w) b hj

theorem haarTape_top (N n u:ℕ) (φ:Config G (R.family.side u n) → ℝ) : haarTape R N n u φ u le_rfl=φ :=
  Nat.decreasingInduction_self ..
theorem haarTape_step {N n u j:ℕ} (φ:Config G (R.family.side u n) → ℝ) (hj:j<u) :
    haarTape R N n u φ j hj.le = fun W=>expect ((H).levels.clock.op j n) ((H).rep N n (j+1)) W
      (haarTape R N n u φ (j+1) hj) := Nat.decreasingInduction_succ_left ..
theorem anchorTape_top (n u:ℕ) (b:Site (R.family.side u n)) : anchorTape R n u b u le_rfl=b :=
  Nat.decreasingInduction_self ..
theorem anchorTape_step {n u j:ℕ} (b:Site (R.family.side u n)) (hj:j<u):
    anchorTape R n u b j hj.le=((H).levels.clock.op j n).ratio.parent (anchorTape R n u b (j+1) hj) :=
  Nat.decreasingInduction_succ_left ..

def fiberRate (j u:ℕ):ℝ := ∏ i∈Finset.Ico j u,Doors.rate ((H).S.block i)

theorem fiberRate_bounds (j u:ℕ) : 0 < fiberRate R j u ∧ fiberRate R j u ≤ 1 :=
  ⟨Finset.prod_pos (fun _ _=>Doors.rate_pos _),Finset.prod_le_one (fun _ _=>(Doors.rate_pos _).le)
    (fun i _=> Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast ((H).S.block i).property) (by norm_num))⟩

theorem transported_wallet (simple:G.Simple) {N n u:ℕ} (cut:u ≤ N)
    (P:Coefficient F0 (R.family.side u n)) (b:Site (R.family.side u n)) (M:ℝ)
    (φ:Config G (R.family.side u n) → ℝ) (form:P.Format b (hol G) ((H).rep N n u))
    (fund:P.remBound b ((H).rep N n u) (kappa H u) M)
    (rep:P.density b D0 ((H).rep N n u)=fun U=>(((H).rep N n u).eval U:ℂ)*(φ U:ℂ))
    (j:ℕ) (hj:j ≤ u) (start:R.t 0 ≤ j) :
    let z:=anchorTape R n u b j hj;let ψ:=haarTape R N n u φ j hj;let A:=(H).rep N n j
    ∃ Q:Coefficient F0 (R.family.side j n), Q.Format z (hol G) A ∧ Q.remBound z A (kappa H j) (fiberRate R j u*M) ∧
      Q.density z D0 A=(fun U=>(A.eval U:ℂ)*(ψ U:ℂ)) ∧
      ∀ U,(ψ U:ℂ)=Q.exponentialEntry z D0 A U+forcedShare Q A U := by
  induction hj using Nat.decreasingInduction with
  | self =>
    dsimp only
    rw [haarTape_top,anchorTape_top,show fiberRate R u u=1 by simp [fiberRate],one_mul]
    refine ⟨P,form,fund,rep,?_⟩
    intro U
    have h:=normalized_entry P ((H).rep N n u) b D0 U (SectorNext.Vacuum.strictly H R.makes.wilson N n u cut U)
    rw [congrFun rep U, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr
      (SectorNext.Vacuum.strictly H R.makes.wilson N n u cut U).ne')] at h
    exact h
  | of_succ j hj ih =>
    let A:=(H).rep N n j;let B:=(H).rep N n (j+1);let K:=(H).levels.clock.op j n
    let w:=anchorTape R n u b (j+1) hj
    let ξ:=haarTape R N n u φ (j+1) hj
    obtain ⟨Y,yform,ydue,ydens,_⟩:=ih (start.trans (Nat.le_succ j))
    obtain ⟨Q,qform,qdens,qdue,_⟩:=run_full_fiber simple R (hj.trans_le cut) start w Y yform ydue
    dsimp only
    rw [haarTape_step R φ hj,anchorTape_step R b hj]
    have rate:fiberRate R j u=Doors.rate ((H).S.block j)*fiberRate R (j+1) u := by
      unfold fiberRate
      rw [←Finset.insert_Ico_add_one_left_eq_Ico hj,Finset.prod_insert (by simp)]
    rw [rate,mul_assoc]
    have pushed:Q.density (K.ratio.parent w) D0 A=K.push B.beta (fun U=>(B.eval U:ℂ)*(ξ U:ℂ)) := by
      rw [qdens,ydens]
    let read:=current_all_boundaries H R.makes.wilson (hj.trans_le cut) (K.ratio.parent w) ξ Q pushed
    refine ⟨Q,qform,qdue,?_,read⟩
    funext U
    have positive:=SectorNext.Vacuum.strictly H R.makes.wilson N n j (hj.le.trans cut) U
    have eq:Q.density (K.ratio.parent w) D0 A U/(A.eval U:ℂ)=(expect K B U ξ:ℂ) :=
      (normalized_entry Q A _ D0 U positive).trans (read U).symm
    rw [mul_comm];exact (div_eq_iff (Complex.ofReal_ne_zero.mpr positive.ne')).mp eq

end YM.Integration.FVA1Physical.Wilson
