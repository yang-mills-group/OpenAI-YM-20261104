import YM.Integration.WilsonSeparatedPrefixKineticWage
import YM.Integration.WilsonVacuumPreResetIndependentForecast

/-! The original elected run pays the finite Hessians and the entire inverse
clock at once, before physical cutoff and period choices. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedPrefixKineticMarket
open Function Finset Filter Lattice Wilson RG RG.Supply Precision PowerSeries
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonSeparatedPrefixKineticWage WilsonOlderFreshSoftSocketKinetic WilsonReportingAbsoluteInletForecastBooks
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "V" => R.family.path.levels

def aperture (b K:ℕ):ℝ:=zz (V) b+(R.family.S.scale K-R.family.S.scale b)+(K-b:ℕ)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)(e:ℕ):
    ∃C:Credit,∀ᶠ b:ℕ in atTop,∀N K,b ≤ K→K ≤ N→
    let M:=(e+2:ℝ)*C.buy (aperture R b K)
    (∀i,b ≤ i→i ≤ K→ mass e (kinetic V R.metals.O N K i) ≤ M) ∧
    (∀i,b ≤ i→i<K→ mass e (pace (pitch V R.metals.O N i)) ≤ M ∧ mass e (pitch V R.metals.O N i) ≤ M):=by
  obtain ⟨C,hC⟩:=window G (e+1) Credit.leanC
  refine ⟨C,?_⟩
  filter_upwards [FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0) (fun _=>1) (fun _=>by decide) e 0 0] with b market N K bK KN
  obtain ⟨Q,run,ratio,clock,base,_⟩:=market
  have localFee (i l:ℕ)(bi:b ≤ i)(il:i ≤ l)(lK:l ≤ K)(tag:Kind):
      mass e (row tag (V) R.metals.O N i (l-i)) ≤ (e+2:ℝ)*C.buy (aperture R b K):=by
    let z:WindowS G (e+1) Credit.leanC:={
        robe:=Q,base:=i,span:=l-i,n:=N,N:=N,b:=K,root:=base.le.trans bi,endS:=by omega,hd:=KN,hg:=KN }
    have age: z.Age ≤ aperture R b K:=by
      have growth:=Q.age b i base.le bi
      have sl:Q.draws.S.scale l ≤ Q.draws.S.scale K:= (OPE.scale_mono Q.draws.S).monotone lK
      rw [run,clock] at growth;rw [run] at sl
      change Q.y i+(Q.draws.S.scale (i+(l-i))-Q.draws.S.scale i)+((l-i:ℕ):ℝ) ≤ _
      rw [clock,run,Nat.add_sub_of_le il];unfold aperture
      have dates:((l-i:ℕ):ℝ) ≤ (K-b:ℕ):=by exact_mod_cast (by omega:l-i ≤ K-b)
      linarith only [growth,sl,dates]
    have purchased:=hC z tag
    change mass (e+1) (row tag Q.draws Q.paid N i (l-i)) ≤ _ at purchased
    rw [run,ratio] at purchased
    have pdown (S:Cost):mass e S ≤ mass (e+1) S:=by
      unfold mass;exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _=>abs_nonneg _)
    have shelf:C.buy z.Age ≤ C.buy (aperture R b K):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans z.warm) age _) (zero_le_one.trans C.good)
    refine (pdown _).trans (purchased.trans ?_)
    simpa only [Nat.cast_add,Nat.cast_one,show ((e:ℝ)+1)+1=e+2 by ring] using
      (mul_le_mul_of_nonneg_left shelf (by positivity:0≤((e+1:ℕ):ℝ)+1))
  dsimp only
  refine ⟨fun i bi iK=>?_,fun i bi iK=>?_⟩
  · rw [socket _ _ _ _ _ iK];exact localFee i K bi iK le_rfl .finer
  · have c:=localFee i (i+1) bi (Nat.le_succ _) iK .coarser
    have h:=localFee i (i+1) bi (Nat.le_succ _) iK .hessian
    simp only [row,Nat.add_sub_cancel_left,(edges ..).2] at c h
    have loc:LocalRatio R.metals.O:=by rw [←ratio];exact Q.green
    rw [hessian _ (angle_tilt (A:=V) simple loc (iK.trans_le KN))] at h
    exact ⟨c,h⟩

end YM.Integration.WilsonSeparatedPrefixKineticMarket
end
