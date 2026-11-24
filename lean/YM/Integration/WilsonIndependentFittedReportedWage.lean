import YM.Integration.WilsonIndependentFittedKineticMass
import YM.Integration.WilsonIndependentMatchedFittedSeat

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedReportedWage
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonOriginalPublicPlantedStableCredit (span)
open WilsonIndependentMatchedFittedSeat (dose)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

theorem matrix (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C:Credit,∀X:CutsP H T p v E W K U,∀j≤e,∀a c:Alma F,
      ‖lineS (CurNames X.ax X.tx T p X.N X.m X.i false) j a c‖≤(Real.exp (span X X.i))^h*C.buy X.Age:=by
  let Z (j:ℕ)(C:Credit):Prop:=∀X:CutsP H T p v E W K U,∀a c:Alma F,
    ‖lineS (CurNames X.ax X.tx T p X.N X.m X.i false) j a c‖≤(Real.exp (span X X.i))^h*C.buy X.Age
  have earn:∀j∈Finset.range (e+1),∃C:Credit,Z j C:=
    fun j hj=>WilsonIndependentFittedForwardLength.cut H T p v E W K U j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  obtain ⟨C,paid⟩:=uniformPays (P:=Z) (Finset.range (e+1)) earn
    (fun j _ _ _ le bill X a c=>(bill X a c).trans (mul_le_mul_of_nonneg_left (le _ X.windowC.warm) (by positivity)))
  exact ⟨C,fun X j hj=>paid j (Finset.mem_range.mpr (by omega)) X⟩

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit):
    ∃C:Credit,∀(X:CutsP H T p v E W K U)(a:ℝ),∀j≤e,∀c:Alma F,
      ‖coeff j (dose X a c)‖≤(Real.exp (span X X.i))^h*C.buy X.Age*(|a| * X.fuel):=by
  obtain ⟨M,mat⟩:=matrix H T p v E W K U
  obtain ⟨C,kin⟩:=WilsonIndependentFittedKineticMass.original G h e E F
  obtain ⟨V,seed⟩:=CutsP.stature H T p v E W K U
  let n:ℝ:=(Fintype.card (Alma F):ℝ)*((e+1:ℕ):ℝ)*2
  let O:=(pur n).prodC (M.prodC (C.prodC V))
  refine ⟨O,fun X a j hj c=>?_⟩
  let f:=(Real.exp (span X X.i))^h
  let m:=M.buy X.Age
  let b:=C.buy X.Age*V.buy X.Age
  let x:=|a| * X.fuel
  have fx:0≤f:=by dsimp [f];positivity
  have mx:0 ≤ m:=zero_le_one.trans (M.purchase X.windowC.warm)
  have cx:0≤C.buy X.Age:=zero_le_one.trans (C.purchase X.windowC.warm)
  have vx:0≤V.buy X.Age:=zero_le_one.trans (V.purchase X.windowC.warm)
  have bx:0≤b:=mul_nonneg cx vx
  have xx:0≤x:=mul_nonneg (abs_nonneg _) X.hf
  let A:=CurNames X.ax X.tx T p X.N X.m X.i false
  let d:=a • X.tileP
  let r:=relativeF X.ax X.tx X.N X.m X.i
  have hm (l:ℕ)(hl:l≤e)(i u:Alma F):twain (f*m) 0 (lineS A l i u) (lineS A l i u):=
    twain.one _ _ le_rfl (mat X l hl i u)
  have top (l:ℕ)(hl:l≤e)(i:Alma F):‖coeff l (d i)‖≤V.buy X.Age*x:=by
    change ‖coeff l (a • X.tileP i)‖≤_
    rw [map_smul,smul_eq_mul,norm_mul,Real.norm_eq_abs]
    calc _≤|a| * (V.buy X.Age*X.fuel):=mul_le_mul_of_nonneg_left (seed X l hl i).main (abs_nonneg _)
         _=_:=by unfold x;ring
  have money (l:ℕ)(hl:l≤e)(i:Alma F):twain (b*x) 0 (coeff l (music r d i)) (coeff l (music r d i)):=by
    apply twain.one _ _ le_rfl
    have sum:=kin X.windowC d (V.buy X.Age*x) (mul_nonneg vx xx) top l hl i
    change ‖coeff l (music r d i)‖≤C.buy X.Age*(V.buy X.Age*x) at sum
    simpa only [b,mul_assoc] using sum
  have actual:=(cargo_rise A A (f*m) b x xx (mul_nonneg fx mx) bx le_rfl hm
    (music r d) (music r d) money j hj c).main
  apply actual.trans
  apply mul_le_mul_of_nonneg_right _ xx
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,O,Credit.products]
  have pay:=mul_le_mul_of_nonneg_right (pure_goal n X.Age) (mul_nonneg mx bx)
  calc _=f*(n*(m*b)):=by unfold n;ring
       _≤f*((pur n).buy X.Age*(m*b)):=mul_le_mul_of_nonneg_left pay fx

end YM.Integration.WilsonIndependentFittedReportedWage
