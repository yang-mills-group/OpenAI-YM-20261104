import YM.Integration.WilsonPositionProgramTrialHomeFaces
/-! Pay the original normalized one-vacuum-to-another comparison at the chosen optical date. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedBufferSalary
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Mosaic
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonIndependentMatchedBufferedVacuum (Receipt stopped)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped BigOperators Topology Classical
variable {G:Gauge}{a h D k u e:ℕ}


open WilsonPositionProgramTrialHomeFaces (Outcome)
def price {a:ℕ}(C wallet:Credit)(clock:ℕ→ℝ)(m:ℕ)(Z:ℝ)(B income:Fin (a+1)→ℝ):ℝ:=
  C.buy Z*∏i,B i*(wallet.buy (clock m)*income i)
theorem receives {Q:Fin (a+1)→SealR G}{L:Levels G}{O:ChartRatio G}{clock:ℕ→ℝ}
    {j:ℕ}{C wallet:Credit}(paid:Receipt Q L O clock j e u C wallet)
    (m K U N N' host:ℕ)(B income:Fin (a+1)→ℝ)(Z ε:ℝ)(b:Herit Q)
    (gone:j ≤ host)(past:host ≤ m)(born:m ≤ K)(gate:K ≤ U)(old:U ≤ N)(new:U ≤ N')
    (warm:1 ≤ clock m)(allowance:Compar L.S clock host m ≤ Z)(funded:∀i,fee b e i ≤ income i)
    (sharp:price C wallet clock m Z B income *trailC L.S m U ≤ ε):
    Outcome Q L O b m K N N' host e u B Z ε:=by
  intro F y o shape
  have fuel i:0 ≤ fee b e i:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have wake:0 ≤ wallet.buy (clock m):=zero_le_one.trans (wallet.purchase warm)
  have pre:=paid m K U N N' host b F B Z y o gone past born gate old new allowance shape
  have charge:C.buy Z*(∏i,B i*(wallet.buy (clock m)*fee b e i)) ≤ price C wallet clock m Z B income:=
    mul_le_mul_of_nonneg_left (prod_le_prod (s:=univ)
      (fun i _=>mul_nonneg (shape.lanes i).1 (mul_nonneg wake (fuel i)))
      (fun i _=>mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (funded i) wake)
        (shape.lanes i).1)) (zero_le_one.trans (C.purchase shape.pos))
  have bound (r t:ℕ)(small':r ≤ e):=
    ((pre.heapS r t small').toll).more ((mul_le_mul_of_nonneg_right charge pre.crest).trans sharp)
  refine ⟨bound,?_⟩
  intro r small' t
  have f:=bound r 0 small'
  have atZero:hedge 0 1 u t*‖((stopped L O Q F b m K N host y o).2 r 0-
      (stopped L O Q F b m K N' host y o).2 r 0) t‖  ≤  ε:=
    (f.2.1.le_tsum t (fun l _=>f.1 l)).trans f.2.2
  rw [autumn_empty G 1 0 u t] at atZero
  simpa only [hedge,autumn,zero_mul,add_zero,one_pow,one_mul,Pi.sub_apply] using atZero

end YM.Integration.WilsonIndependentMatchedBufferSalary
end
