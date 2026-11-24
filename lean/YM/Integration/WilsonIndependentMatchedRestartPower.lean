import YM.Integration.WilsonIndependentMatchedRestartVacuum
import YM.Integration.WilsonOriginalPublicTwoTopOpening
import YM.Integration.WilsonIndependentMatchedCoverJoined

/-! Both programmes plant their complete normalized fields at K. One cold
programme inherits its old vacuum from N, while the other's vacuum begins
at that same K. The reporting vector is common to their distinct lifts. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentMatchedRestartPower
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}

open WilsonIndependentMatchedRestartVacuum (Receipt reading)
variable {Q:Fin (a+1)→SealR G}{L:Levels G}{O:ChartRatio G}{clock:ℕ→ℝ}
    {j m K N:ℕ}{C wallet:Credit}

def amount (_Q:Fin (a+1)→SealR G)(L:Levels G)(clock:ℕ→ℝ)(C wallet:Credit)(B income η:Fin (a+1)→ℝ)
    (Z:ℝ)(m K:ℕ):ℝ:=
  C.buy Z*(∏i,B i*(wallet.buy (clock m)*income i))*
    (L.S.a K/L.S.a m)^((1/4:ℝ)-∑i,η i)

theorem returned (paid:Receipt Q L O clock j e u C wallet)
    (b:Herit Q)(F:Wilt Q)(B income η:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ m)(base:m ≤ K)(fine:K ≤ N)(warm:1 ≤ clock m)(room:clock m ≤ Z)(shape:Bough Q F y Z B)
    (bought:∀i,fee b e i ≤ income i*(L.S.a K/L.S.a m)^(-η i))
    (r t:ℕ)(small:r ≤ e):
    Fruit 0 1 u ((reading L O Q F b m K N y o).2 r t-
      (reading L O Q F b m K K y o).2 r t) (amount Q L clock C wallet B income η Z m K):=by
  let δ:=L.S.a K/L.S.a m
  have hd:0<δ:=div_pos (L.S.a_pos K) (L.S.a_pos m)
  have cw:0 ≤ wallet.buy (clock m):=zero_le_one.trans (wallet.purchase warm)
  have cz:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase shape.pos)
  let cost i:=B i*(wallet.buy (clock m)*income i)
  have bound i:B i*(wallet.buy (clock m)*fee b e i) ≤ cost i*δ^(-η i):=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bought i) cw) (shape.lanes i).1).trans_eq (by dsimp [δ,cost];ring)
  have fpos i:0 ≤ fee b e i:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have both:(∏i,B i*(wallet.buy (clock m)*fee b e i)) ≤ (∏i,cost i)*∏i,δ^(-η i):=
    (prod_le_prod (s:=univ) (fun i _=>mul_nonneg (shape.lanes i).1 (mul_nonneg cw (fpos i)))
      (fun i _=>bound i)).trans_eq prod_mul_distrib
  have powers:(∏i,δ^(-η i))=δ^(-(∑i,η i)):=by
    rw [←sum_neg_distrib,Real.rpow_sum_of_pos hd]
  have step:=((paid m K N b F B Z y o awake base fine room shape).heapS r t small).toll
  apply step.more
  rw [WilsonOriginalPublicTwoTopOpening.clock]
  change C.buy Z * _ * δ^(1/4:ℝ) ≤ (C.buy Z*(∏i,cost i))*δ^((1/4:ℝ)-∑i,η i)
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left both cz) (Real.rpow_nonneg hd.le _)).trans_eq ?_
  rw [powers,mul_assoc,mul_assoc,←Real.rpow_add hd]
  ring_nf

theorem ordinary (paid:Receipt Q L O clock j e u C wallet)
    (b:Herit Q)(F:Wilt Q)(B income η:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR)
    (awake:j ≤ m)(base:m ≤ K)(fine:K ≤ N)(warm:1 ≤ clock m)(room:clock m ≤ Z)(shape:Bough Q F y Z B)
    (bought:∀i,fee b e i ≤ income i*(L.S.a K/L.S.a m)^(-η i))
    (r:ℕ)(hr:r ≤ e)(t:Fin 0→YForest G):
    ‖(reading L O Q F b m K N y o).2 r 0 t-(reading L O Q F b m K K y o).2 r 0 t‖ ≤ 
      amount Q L clock C wallet B income η Z m K:=by
  have h:=returned paid b F B income η Z y o awake base fine warm room shape bought r 0 hr
  have at₀:hedge 0 1 u t*‖((reading L O Q F b m K N y o).2 r 0-(reading L O Q F b m K K y o).2 r 0) t‖ ≤ _:=
    (h.2.1.le_tsum t (fun l _=>h.1 l)).trans h.2.2
  rw [autumn_empty G 1 0 u t] at at₀
  simpa only [hedge,autumn,zero_mul,add_zero,one_pow,one_mul,Pi.sub_apply] using at₀

end YM.Integration.WilsonIndependentMatchedRestartPower
