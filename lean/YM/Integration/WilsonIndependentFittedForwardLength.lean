import YM.Integration.WilsonIndependentFittedForwardCourse
import YM.Integration.WilsonOriginalPublicPlantedStableCredit

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedForwardLength
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open WilsonIndependentFittedForwardStep WilsonIndependentFittedForwardCourse
open scoped BigOperators Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

theorem lengths (S:Schedule)(m n:ℕ):
    (∏i∈Finset.range n,((S.block (m+i)).val:ℝ))=Real.exp (S.scale (m+n)-S.scale m):=by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [Finset.prod_range_succ,ih,Nat.add_succ,S.scale_succ,
      show S.scale (m+n)+Real.log (S.block (m+n)).val-S.scale m=
        (S.scale (m+n)-S.scale m)+Real.log (S.block (m+n)).val by ring,
      Real.exp_add,Real.exp_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (S.block (m+n)).property)]

def factor (t:CourseS H T p e E W U):ℝ:=
  (Real.exp (t.vols.draws.S.scale (t.spur+t.length)-t.vols.draws.S.scale t.spur))^h
theorem positive (t:CourseS H T p e E W U):0<factor t:=pow_pos (Real.exp_pos _) _

theorem restored (t:CourseS H T p e E W U)(n:ℕ)(b:Bool):
    hillcrest (normalized t n b) t.length=(factor t)⁻¹ • CurNames t.vols.draws t.vols.paid T p n t.spur t.length b:=by
  unfold normalized CurNames
  rw [restore]
  congr 1
  change (∏i∈Finset.range t.length,((((t.vols.draws.S.block (t.spur+i)).val:ℝ)^h)⁻¹))=_
  rw [Finset.prod_inv_distrib,Finset.prod_pow,lengths]
  rfl

theorem refund {x y w A δ:ℝ}(positive:0<w)(paid:twain A δ (w⁻¹*x) (w⁻¹*y)):
    twain (w*A) δ x y:=by
  have gain (z t:ℝ)(bound:‖w⁻¹*z‖≤t):‖z‖≤w*t:=by
    rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr positive.le),←div_eq_inv_mul,div_le_iff₀ positive] at bound
    simpa only [mul_comm w] using bound
  refine ⟨gain _ _ paid.main,gain _ _ paid.side,?_⟩
  rw [mul_assoc]
  apply gain
  simpa only [mul_sub] using paid.gap

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(e:ℕ)(E W U:Credit)(b:Bool)(i:ℕ)(hi:i≤e):
    ∃C:Credit,∀t:CourseS H T p e E W U,∀a c:Alma F,
      let M n:=CurNames t.vols.draws t.vols.paid T p n t.spur t.length b
      twain (factor t*C.buy t.Age) t.cab (lineS (M t.I.n) i a c) (lineS (M t.I.N) i a c):=by
  obtain ⟨C,paid⟩:=normalized_price H T p e E W U b i hi
  refine ⟨C,fun t a c=>?_⟩
  have own:=paid t a c
  rw [restored,restored,line,line] at own
  exact refund (positive t) own

theorem cut (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit)(i:ℕ)(hi:i≤e):
    ∃C:Credit,∀X:CutsP H T p v E W K U,∀a c:Alma F,
      ‖lineS (CurNames X.ax X.tx T p X.N X.m X.i false) i a c‖≤
        (Real.exp (WilsonOriginalPublicPlantedStableCredit.span X X.i))^h*C.buy X.Age:=by
  obtain ⟨C,paid⟩:=original H T p e E W U false i hi
  refine ⟨C,fun X a c=>?_⟩
  let t:CourseS H T p e E W U:=⟨X.L',X.windowC,by rw [X.he];rfl⟩
  have rate:=(paid t a c).main
  change ‖lineS (CurNames X.L'.arch.V.draws X.L'.arch.V.paid T p X.N X.m X.i false) i a c‖≤
    (Real.exp (X.L'.arch.V.draws.S.scale (X.m+X.i)-X.L'.arch.V.draws.S.scale X.m))^h*C.buy X.Age at rate
  rwa [X.he] at rate

end YM.Integration.WilsonIndependentFittedForwardLength
