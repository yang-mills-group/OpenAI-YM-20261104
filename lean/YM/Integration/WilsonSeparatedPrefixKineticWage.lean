import YM.Integration.WilsonOlderFreshSoftSocketKinetic
import YM.Integration.WilsonMarkedIndependentReporterFinance
import YM.Integration.FundedMarkedCoverRows
import YM.Integration.WilsonSeparatedPrefixKineticTruncation

/-! Pay both directions of the true relative chart and the Hessian evaluated
at the finer coupling on the allotted finite original interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticWage
open Function Finset Filter Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Realm
open PhysicalNext.Repeat.Legato WilsonOlderFreshSoftSocketKinetic WilsonReportingAbsoluteInletForecastBooks
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Shard
open Source Source.Drops Labels
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem edges (A:Levels G)(O:ChartRatio G)(N i:ℕ):
    relativeF A O N i 1=ratioHigh A O N i ∧ relativeC A O N i 1=pace (pitch A O N i):=by
  simp [relativeF,relativeC,palmB,leeB,chart_one]

theorem socket (A:Levels G)(O:ChartRatio G)(N K i:ℕ)(iK:i ≤ K):
    kinetic A O N K i=relativeF A O N i (K-i):=by
  induction iK using Nat.decreasingInduction with
  | self=>simp [kinetic,relativeF,palmB]
  | of_succ i hi ih=>
    rw [kinetic,dif_pos hi,ih,show K-i=1+(K-(i+1)) by omega,stageF,(edges ..).1]

theorem backwards (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    {N K i:ℕ}(iK:i<K)(KN:K ≤ N):
    chartB (kinetic A O N K i) (pace (pitch A O N i))=kinetic A O N K (i+1):=by
  rw [kinetic,dif_pos iK,chart_assoc]
  have h:=chart_forward (angle_tilt (A:=A) simple localO (iK.trans_le KN))
  rw [show chartB (ratioHigh A O N i) (pace (pitch A O N i))=1 from h,chart_one]

theorem hessian (H:Cost)(one:constantCoeff H=1):(pace H)⁻¹^2=H:=by
  let T:=pace H
  have unit:constantCoeff T=1:=pace_cc one
  have cash:T*T⁻¹=1:=PowerSeries.mul_inv_cancel T (by rw [unit];exact one_ne_zero)
  have nz:T≠0:=by intro h;rw [h,zero_mul] at cash;exact zero_ne_one cash
  apply mul_right_cancel₀ (b:=T^2) (pow_ne_zero _ nz)
  calc
    _=(T*T⁻¹)^2:=by dsimp [T];ring
    _=1:=by rw [cash,one_pow]
    _=_:=(pace_tax one).symm

inductive Kind | finer | coarser | hessian deriving Fintype,DecidableEq

def row (k:Kind)(A:Levels G)(O:ChartRatio G)(N b h:ℕ):Cost:=
  match k with
  | .finer=>relativeF A O N b h
  | .coarser=>relativeC A O N b h
  | .hessian=>(relativeC A O N b h)⁻¹^2

private theorem budget (G:Gauge)(e:ℕ)(E:Credit)(i:ℕ)(ie:i ≤ e)(k:Kind):
    Weft (WindowS.Age (G:=G) (e:=e) (U:=E)) WindowS.cab
      (fun t=>row k t.robe.draws t.robe.paid t.n t.base t.span)
      (fun t=>row k t.robe.draws t.robe.paid t.N t.base t.span) i:=by
  cases k with
  | finer=>exact ascend G e i E ie
  | coarser=>exact descend G e i E ie
  | hessian=>
    let Cs (t:WindowS G e E)(N:ℕ):=relativeC t.robe.draws t.robe.paid N t.base t.span
    have lower (j:ℕ)(hj:j ≤ i):Weft WindowS.Age WindowS.cab
        (fun t:WindowS G e E=>(Cs t t.n)⁻¹) (fun t=>(Cs t t.N)⁻¹) j:=by
      apply clipped_inv (WindowS.payments G e E)
      · intro t;exact angularC t.robe.hG t.robe.green (t.endS.trans t.hd)
      · intro t;exact angularC t.robe.hG t.robe.green (t.endS.trans t.hg)
      · intro l hl;exact descend G e l E (hl.trans (hj.trans ie))
    exact clipped_pow (WindowS.payments G e E) 2 lower

theorem window (G:Gauge)(e:ℕ)(E:Credit):∃B:Credit,∀t:WindowS G e E,∀k,
    mass e (row k t.robe.draws t.robe.paid t.n t.base t.span)  ≤  (e+1:ℝ)*B.buy t.Age:=by
  let S:=(range (e+1))×ˢ(univ:Finset Kind)
  let P (s:ℕ×Kind)(B:Credit):Prop:=∀t:WindowS G e E,
    |coeff s.1 (row s.2 t.robe.draws t.robe.paid t.n t.base t.span)| ≤ B.buy t.Age
  have each:∀s∈S,∃B:Credit,P s B:=by
    rintro ⟨i,k⟩ hk
    obtain ⟨d,C,_,sold⟩:=budget G e E i (mem_range_succ_iff.mp (mem_product.mp hk).1) k
    refine ⟨⟨d,max 1 C,le_max_left ..⟩,fun t=>?_⟩
    exact (sold t).main.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans t.warm) _))
  obtain ⟨B,priced⟩:=uniformPays (P:=P) S each
    (fun i _ _ _ le paid t=>(paid t).trans (le _ t.warm))
  refine ⟨B,fun t k=>?_⟩
  calc
    _ ≤ ∑_i∈range (e+1),B.buy t.Age:=sum_le_sum fun i hi=>priced (i,k) (mem_product.mpr ⟨hi,mem_univ _⟩) t
    _=_:=by simp

end YM.Integration.WilsonSeparatedPrefixKineticWage
end
