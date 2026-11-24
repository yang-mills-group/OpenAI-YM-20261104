import YM.Integration.WilsonOriginalPublicTwoTopInvoice
import YM.Integration.WilsonPositionProgramTrialCollarMesh

/-! Choose the physical depth after the public norm and the shape bill. The
kinetic clock and both tops refer to the elected physical schedule. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicTwoTopOpening
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonOriginalPublicTwoTopJoined (Hearing)
open WilsonOriginalPublicTwoTopInvoice (dose bill)
open scoped Topology BigOperators Classical
variable {G : Gauge} {a e u : ℕ}

theorem clock {K m : ℕ} (S : Schedule) :
    trailC S m K = (S.a K/S.a m)^(1/4:ℝ) := by
  have h : 0 < S.a K/S.a m := div_pos (S.a_pos K) (S.a_pos m)
  rw [Real.rpow_def_of_pos h, ← show paceT S m K=S.a K/S.a m from rfl,
    pace_rep,Real.log_exp]
  unfold trailC
  congr 1
  ring

theorem physical (R : Run G) (D : XSpace.Run) {start stage n j b : ℕ} {w : ℕ → ℕ}
    (room : WilsonPositionProgramTrialCollarMesh.Corridor R D start w stage n j b) :
    trailC R.family.S (start+n) (start+n+j) =
      ((D.step (WilsonPositionProgramTrialCollarMesh.index w n j)).spacing)^(1/4:ℝ) := by
  rw [clock,room.spacing]

variable (R : Run G)(W : Initialize G)(B : Local.Physical.Deck G)
    (l d : Fin (a+1) → ℕ)(fit : ∀ i,l i<d i)
    (I : Fin (a+1) → Type) [∀ i,Fintype (I i)] (leg : (i : Fin (a+1)) → I i → Glyph B (l i))
    (p : Fin (a+1) → ℂ →L[ℝ] ℝ)

local notation "L" => R.family.path.levels
local notation "Q" => deck (G:=G) l d fit
local notation "E" => fun i : Fin (a+1) => R.family.labels.level (l i)

def entry (e : ℕ) (i : Fin (a+1)) : ℝ :=
  Fintype.card (Alma (E i))*(e+1:ℕ)*(‖p i‖*bill W (E i) (leg i))

include fit in
theorem original {j m K N : ℕ} {C C' wallet : Credit}
    (heard : Hearing Q L R.metals.O (zz L) j e u C C' wallet)
    (F : Wilt Q) (prices : Fin (a+1) → ℝ) (Z y : ℝ) (o : CellR)
    (open' : j ≤ m)(base : m ≤ K)(fine : K ≤ N)(room : zz L m ≤ Z)
    (shape : Bough Q F y Z prices)(nn : ∀ i,0 ≤ prices i) (c0 : 0 ≤ C.buy Z)(w0 : 0 ≤ wallet.buy (zz L m))
    (P D s : ℝ)(d₀ : Fin (a+1) → ℝ)
    (budget : 2*C.buy Z*(∏ i, prices i*(wallet.buy (zz L m)*entry R W B l I leg p e i))
      ≤ Real.exp (D*s))
    (deep : 4*(P+D+∑ i,d₀ i)*s ≤ (L).S.scale K-(L).S.scale m)
    (x : (i : Fin (a+1)) → I i → ℂ) (funded : ∀ i, ‖x i‖ ≤ Real.exp (d₀ i*s))
    (r t : ℕ) (low : r ≤ e) :
    let X := dose R W B l d fit I leg x p
    let v := normalized L R.metals.O Q X m N
    Fruit 0 1 u ((loadK L R.metals.O F v m N N y o).2 r t -
      (loadK L R.metals.O F v m K N y o).2 r t) (Real.exp (-P*s)) := by
  intro X v
  have note := ((heard m K N X F prices Z y o open' base fine room shape).2.1.heapS r t low).toll
  apply note.more
  let w := wallet.buy (zz L m)
  let cost (i : Fin (a+1)) := prices i*(w*entry R W B l I leg p e i)
  have paid i : prices i*(w*fee X e i) ≤ cost i * ‖x i‖ := by
    have h := WilsonOriginalPublicTwoTopInvoice.original R W B l d fit I leg x p e i
    have seen : fee X e i ≤ entry R W B l I leg p e i*‖x i‖ := by
      apply h.trans_eq
      unfold entry
      ring
    calc
      _ ≤ prices i*(w*(entry R W B l I leg p e i*‖x i‖)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left seen w0) (nn i)
      _ = _ := by dsimp [cost];ring
  have fpos i : 0 ≤ fee X e i := sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _
  have both : (∏i,prices i*(w*fee X e i)) ≤ (∏i,cost i)*∏i,‖x i‖ :=
    (prod_le_prod (s:=univ) (fun i _=>mul_nonneg (nn i) (mul_nonneg w0 (fpos i))) (fun i _=>paid i)).trans_eq
      Finset.prod_mul_distrib
  have xx : ∏ i,‖x i‖ ≤ Real.exp ((∑ i,d₀ i)*s) := by
    calc
      _ ≤ ∏ i, Real.exp (d₀ i*s) := prod_le_prod (fun i _=>norm_nonneg _) (fun i _ =>funded i)
      _ = _ := by rw [←Real.exp_sum,Finset.sum_mul]
  have depth : trailC (L).S m K ≤ Real.exp (-(P+D+∑ i,d₀ i)*s) := by
    unfold trailC
    apply Real.exp_le_exp.mpr
    linarith
  have pref : 2*(C.buy Z*∏ i,prices i*(w*fee X e i)) ≤ Real.exp (D*s)*Real.exp ((∑ i,d₀ i)*s) := by
    calc
      _ ≤ 2*(C.buy Z*((∏ i,cost i)*∏ i,‖x i‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left both c0) (by norm_num)
      _ = (2*C.buy Z*∏ i,cost i)*∏ i,‖x i‖ := by ring
      _ ≤ _ := mul_le_mul budget xx (prod_nonneg (fun i _=>norm_nonneg _)) (Real.exp_pos _).le
  calc
    _ ≤ (Real.exp (D*s)*Real.exp ((∑ i,d₀ i)*s))*Real.exp (-(P+D+∑ i,d₀ i)*s) :=
      mul_le_mul pref depth (Real.exp_pos _).le (by positivity)
    _ = Real.exp (-P*s) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
end YM.Integration.WilsonOriginalPublicTwoTopOpening
end
