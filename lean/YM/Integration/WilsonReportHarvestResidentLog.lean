import YM.RG05Readout.Many.Stage
import YM.MergeProof.Pitch
import YM.MergeProof.Endow
import YM.FormalOPE.RG10.MarkerLog

/-! The full normalized conditional mixed coefficient on the healthy Wilson sector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentLog
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil RG05Readout.Many Extra.Trajectories
open scoped BigOperators Classical Topology
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] [Fintype V] {J:Census V}

private theorem emptyProfile (P:Activities G n) (f:ℕ → Config G n → ℂ) (i:Box n) (barren:¬i.2.Nonempty) (U:Config G n):profile P f i U=0:=by
  letI : IsEmpty {j:ℕ//barcode P j=i}:=⟨fun j=>barren (by rw [←j.property];exact (P.forced j.val).inventory_ne)⟩
  simp [profile,cram]

omit [Fintype V] in
private theorem emptyGas (ν:Box n → Poly J) (no:∀i,¬i.2.Nonempty → ν i=0):field ν ∅=1:=by
  unfold field;rw [Finset.sum_eq_single ∅]
  · unfold grid;rw [if_pos (show Pattern (∅:Support n) ∅ from ⟨by simp,rfl⟩)];simp
  · intro X _ nonempty
    unfold grid;split_ifs with allowed
    · obtain ⟨i,member⟩:=Finset.nonempty_iff_ne_empty.mpr nonempty
      have empty:i.2⊆(∅:Support n):=allowed.2 ▸ (show i.2⊆X.biUnion (fun j=>j.2) from subset_biUnion_of_mem _ member)
      exact Finset.prod_eq_zero member (no i (fun h=>absurd (h.mono empty) Finset.not_nonempty_empty))
    · rfl
  · simp

variable (P:Rep G n) (rows:V → RG05Readout.Address.Three G n) {o:V → Site n}
    {H:Support n → Config G n → Poly J} {K:Box n → Config G n → Poly J}

private theorem restored (legal:Carton o H K P.p.threshold) (U:Config G n) (clear:flags P.p.threshold U=∅):
    restore P (fun i=>(rows i).2.1) (fun i=>profile P.activities (rows i).2.2) H K U=
      (P.eval U:ℂ) • Poly.pass (Mach J (fun i=>(rows i).2.1 U)+∑S,H S U):=by
  have blank (i:Box n) (empty:¬i.2.Nonempty):bar P.activities J U i+Mach J (fun v=>profile P.activities (rows v).2.2 i U)+K i U=0:=by
    have k:K i U=0:=by by_contra nz;exact empty (((legal.flag i).1.permits U nz).2.1)
    have base:bar P.activities J U i=0:=by unfold bar;rw [emptyProfile _ _ i empty U,map_zero]
    rw [k,base];unfold Mach;simp_rw [emptyProfile _ _ i empty U,Poly.send_zero];simp
  rw [restore,clear,emptyGas _ blank,mul_one,Rep.eval,Activities.gas_one _ _ clear,mul_one]

variable {P rows} {w:V → ℝ} {α ρ:ℝ} {Z:Config G n → Poly J}

/-- The exact full normalized mixed log on the empty physical flag sector, using one original sum budget at the marked site. -/
theorem original (board:MenuBoard P rows Z o w α ρ)(wp:∀v,0<w v)(expo:0 ≤ α)
    (U:Config G n)(clear:flags P.p.threshold U=∅)(s:J.Mode)(size:2 ≤ s.val.card)
    (a b:V)(ha:a∈s.val)(hb:b∈s.val)(d:ℕ)
    (far:d*(4*P.p.B+2)+2*P.p.B<separation (o a) (o b)):
    Poly.toll w s*‖(connected ((P.eval U:ℂ)⁻¹ • Z U)).part s‖ ≤ Real.exp (-α*(d:ℝ))*ρ:=by
  obtain ⟨H,K,legal,hH,_,actual⟩:=board.grants
  let log:=Mach J (fun i=>(rows i).2.1 U)+∑S,H S U
  have nonzero:(P.eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (by
    rw [Rep.eval,Activities.gas_one _ _ clear,mul_one];exact (Real.exp_pos _).ne')
  have density:((P.eval U:ℂ)⁻¹ • Z U)=Poly.pass log:=by
    dsimp only [log];rw [actual,restored P rows legal U clear,smul_smul,inv_mul_cancel₀ nonzero,one_smul]
  have silent:log.part J.quiet=0:=by
    dsimp only [log];rw [Poly.part_plus,mute,Poly.part_sum];simp only [(legal.exp _).1.sil];simp
  rw [density,FormalOPE.RG10.PolyUtil.conn_pass _ silent]
  dsimp only [log];rw [Poly.part_plus,hush _ _ size,zero_add,Poly.part_sum]
  obtain ⟨wallet,_,bill,atoms⟩:=hH
  have major:=budget_scale (Real.exp_pos (-α*(d:ℝ))).le (bill (o a))
  have budget:SumBudget (fun X:Support n=>Poly.toll w s*‖(H X U).part s‖) (Real.exp (-α*(d:ℝ))*ρ):=by
    apply budget_mono major
    · intro X;exact mul_nonneg (Poly.worth wp s).le (norm_nonneg _)
    intro X
    by_cases active:(H X U).part s=0
    · rw [active,norm_zero,mul_zero];exact major.1 X
    have rooted:(s.val:Set V) ⊆ {v|o v∈X}:=by
      by_contra missing;exact active ((legal.exp X).1.toBorne.scope U s missing)
    have extent:=Corona.extent X P.p.B (rooted ha) (rooted hb)
    have reach:d ≤ coverNumber P.p.B X:=by
      by_contra! short;exact (not_le_of_gt far) (extent.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ short.le) _))
    have depth:(d:ℝ) ≤ (coverNumber P.p.B X:ℝ):=by exact_mod_cast reach
    have move:1 ≤ Real.exp (-α*(d:ℝ))*Real.exp (α*(coverNumber P.p.B X:ℝ)):=by
      rw [←Real.exp_add];apply Real.one_le_exp;linarith only [mul_le_mul_of_nonneg_left depth expo]
    have paid:Poly.toll w s*‖(H X U).part s‖ ≤ wallet X:=(Poly.member wp s _).trans ((atoms X).fares wp |>.2 U)
    change _ ≤ Real.exp (-α*(d:ℝ))*(if o a∈X then wallet X*Real.exp (α*(coverNumber P.p.B X:ℝ)) else 0)
    rw [if_pos (show o a∈X from rooted ha)]
    calc
      _ ≤ wallet X:=paid
      _ ≤ wallet X*(Real.exp (-α*(d:ℝ))*Real.exp (α*(coverNumber P.p.B X:ℝ))):=
        le_mul_of_one_le_right ((atoms X).fares wp).1 move
      _ = _:=by ring
  have total:=budget.2.2
  rw [tsum_fintype] at total
  exact (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Poly.worth wp s).le).trans (by simpa only [Finset.mul_sum] using total)

end YM.Integration.WilsonReportHarvestResidentLog
