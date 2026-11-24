import YM.Integration.WilsonPositionProgramTrialPaidHome
import YM.Integration.WilsonIndependentMatchedBufferedVacuum
import YM.Integration.WilsonOriginalPublicTwoTopOpening

/-! A fixed birth on either complete vacuum, with the buffer chosen before the measured sources. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialBufferedHome
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

theorem shrinks (S:Schedule)(m:ℕ):Tendsto (trailC S m) atTop (𝓝 0):=by
  have sizes:Tendsto (fun n=>S.a n/S.a m) atTop (𝓝 0):=by simpa using S.shrinks.div_const (S.a m)
  have powers:Continuous (fun x:ℝ=>x^(1/4:ℝ)):=Real.continuous_rpow_const (by norm_num)
  have s:=powers.continuousAt.tendsto.comp sizes
  change Tendsto (fun n=>trailC S m n) atTop (𝓝 0)
  simpa only [WilsonOriginalPublicTwoTopOpening.clock,Function.comp_def,
    Real.zero_rpow (by norm_num : (1/4:ℝ)≠0)] using s

def Stable (Q:Fin (a+1)→SealR G)(L:Levels G)(O:ChartRatio G)(clock:ℕ→ℝ)(j e u:ℕ):Prop:=
  ∀m K host:ℕ,j ≤ host → host ≤ m → m ≤ K →
  ∀(B income:Fin (a+1)→ℝ)(Z ε:ℝ),
    1≤clock m → Compar L.S clock host m ≤ Z → 0<ε →
    ∃upper:ℕ,K ≤ upper ∧ ∀N N' (b:Herit Q)(F:Wilt Q)(y:ℝ)(o:CellR),
      upper ≤ N → upper ≤ N' → Bough Q F y Z B → (∀i,fee b e i ≤ income i) →
      let old:=stopped L O Q F b m K N host y o
      let new:=stopped L O Q F b m K N' host y o
      (∀r t,r≤e → Fruit 0 1 u (old.2 r t-new.2 r t) ε) ∧
      ∀r,r≤e → ∀t:Fin 0→YForest G,‖old.2 r 0 t-new.2 r 0 t‖≤ε

theorem release {Q:Fin (a+1)→SealR G}{L:Levels G}{O:ChartRatio G}{clock:ℕ→ℝ}
    {j:ℕ}{C wallet:Credit}(paid:Receipt Q L O clock j e u C wallet):
    Stable Q L O clock j e u:=by
  intro m K host gone past start B income Z ε warm allowance small
  let bill:=C.buy Z*∏i,B i*(wallet.buy (clock m)*income i)
  have toZero:Tendsto (fun n=>bill*trailC L.S m n) atTop (𝓝 0):=by
    simpa only [mul_zero] using (shrinks L.S m).const_mul bill
  obtain ⟨upper,near,clears⟩:=(((tendsto_order.1 toZero).2 ε small).and (eventually_ge_atTop K)).exists
  refine ⟨upper,clears,?_⟩
  intro N N' b F y o old new shape funded
  have fuel i:0≤fee b e i:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have wake:0≤wallet.buy (clock m):=zero_le_one.trans (wallet.purchase warm)
  have pre:=paid m K upper N N' host b F B Z y o gone past start clears old new allowance shape
  have charge:C.buy Z*(∏i,B i*(wallet.buy (clock m)*fee b e i))≤bill:=
    mul_le_mul_of_nonneg_left (prod_le_prod (s:=univ)
      (fun i _=>mul_nonneg (shape.lanes i).1 (mul_nonneg wake (fuel i)))
      (fun i _=>mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (funded i) wake)
        (shape.lanes i).1)) (zero_le_one.trans (C.purchase shape.pos))
  have bound (r t:ℕ)(small':r≤e):=
    ((pre.heapS r t small').toll).more ((mul_le_mul_of_nonneg_right charge pre.crest).trans near.le)
  refine ⟨bound,?_⟩
  intro r small' t
  have f:=bound r 0 small'
  have atZero:hedge 0 1 u t*‖((stopped L O Q F b m K N host y o).2 r 0-
      (stopped L O Q F b m K N' host y o).2 r 0) t‖ ≤ ε:=
    (f.2.1.le_tsum t (fun l _=>f.1 l)).trans f.2.2
  rw [autumn_empty G 1 0 u t] at atZero
  simpa only [hedge,autumn,zero_mul,add_zero,one_pow,one_mul,Pi.sub_apply] using atZero

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e)(l d:Fin (a+1)→ℕ)(admit:∀i,l i<d i)
    (cap:capP (deck (G:=G) l d admit)≤k):
    ∀ᶠ j:ℕ in atTop,Stable (deck (G:=G) l d admit) R.family.path.levels R.metals.O
      (zz R.family.path.levels) j e u:=by
  obtain ⟨_,_,sale⟩:=WilsonIndependentMatchedBufferedVacuum.original R simple v funded fit rails l d admit cap
  exact sale.mono fun _ paid=>release paid

end YM.Integration.WilsonPositionProgramTrialBufferedHome
end
