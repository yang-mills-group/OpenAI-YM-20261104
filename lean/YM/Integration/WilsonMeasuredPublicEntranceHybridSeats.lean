import YM.Integration.WilsonMeasuredPublicEntranceTrialTariff
import YM.Integration.WilsonSeparatedPrefixCanonicalMounted

/-! One actual positive wallet for ordinary peers from either original
carrier and any independently received canonical hard row. It keeps the
returned trial field, the canonical regular field and their constants. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceHybridSeats
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal
open Push.Local Push.AbsoluteSums MergeProof MergeProof.Accent PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Lodestar Extra.Histories WilsonOriginalStarPrimaryCatalog WilsonRetainedMarkedInletRegular Trace.Physical.GermGraph
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels

theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ f:ℕ in atTop,∀N p, f≤N → ((A).params f).supportExponent=100 →
    ∀(o:V → Site ((C).side f p))(q:∀i,Coefficient ((C).labels.level (d i)) ((C).side f p))
      (B D w₀ wY:V → ℝ),
    let P:=(C).path.rep N p f
    let a:=fun v=>WilsonSeparatedPrefixCanonicalMounted.salary R d f p q B v + (wY v)⁻¹
    let w:=WilsonSeparatedPrefixCanonicalWallet.seat w₀ a D
    let μ:=fun v=>w v^2
    ∀ {X I:Type},∀ [Countable I],∀(Y:Lamps X I G P.p o (Marks V))(x:X),
    (∀i,0<w₀ i) → (∀i,0<wY i) → (∀i,0≤D i) →
    (∀i,(C).ref (d i)≤f) → (∀i,(q i).Format (o i) (C).params P) →
    (∀i,(q i).remBound (o i) P (LocalComparison.forcedDivisor (C) f) (B i)) →
    Y.Paid wY P.p.B (P.p.supportExponent-1) 1 →
    (∀i,0<w i) ∧ (∀i, μ i≤w₀ i) ∧ (∀i,(μ i)⁻¹=WilsonSeparatedPrefixCanonicalWallet.debit w₀ a D i) ∧
    (∀i, μ i*D i≤1/8) ∧ (∑i,μ i*a i)≤1/8 ∧
    ∀trial:Finset V,let field:=fun i U=>if i∈trial then (Y.log x U).part ((Marks V).fire i)
        else (q i).exponentialEntry (o i) ((C).localSection (d i)) P U
    ∃(c:V → Poly (Marks V))(M:V → Support ((C).side f p) → Config G ((C).side f p) → Poly (Marks V)),
      (∀i,(c i).part (Marks V).quiet=0) ∧
      (∀i,Poly.price μ (c i)≤(Fintype.card V:ℝ)*(μ i*a i)) ∧
      (∀i Z,Burns o Z (M i Z) P.p.threshold) ∧
      (∀i,Towed μ id (M i) P.p.B (P.p.supportExponent-1) (μ i*a i)) ∧
      ∀i U,Poly.send ((Marks V).fire i) (field i U)=c i+∑Z,M i Z U:=by
  have atDates:=Filter.eventually_all.mpr (fun i:V=>WilsonSeparatedPrefixCanonicalIncome.original R (d i) simple pace wage)
  filter_upwards [atDates] with f earned N p live fixed o q B D w₀ wY P a w μ X I count Y x fresh payment dn ref fit fee bounded
  letI:Countable I:=count
  have base:P.p=(A).budget f:=(R.makes.wilson.represents N p f live).vac
  have alpha:P.p.supportExponent=100:=by rw [base];exact fixed
  have bn(i):0≤B i:=rem_nonneg (fee i)
  have old(i):0≤WilsonSeparatedPrefixCanonicalMounted.salary R d f p q B i:=by
    unfold WilsonSeparatedPrefixCanonicalMounted.salary
    exact add_nonneg (mul_nonneg (by positivity) (by unfold Frame.coeffSize;positivity)) (mul_nonneg (sq_nonneg _) (bn _))
  have an(i):0≤a i:=add_nonneg (old i) (inv_nonneg.mpr (payment i).le)
  obtain ⟨wp,within,real,soft,hard⟩:=WilsonSeparatedPrefixCanonicalWallet.original w₀ a D fresh an dn
  have mp(i):0<μ i:=sq_pos_of_pos (wp i)
  have ind(i:V): μ i*D i≤1/8:=(Finset.single_le_sum (fun j _=>mul_nonneg (mp j).le (dn j)) (mem_univ i)).trans hard
  refine ⟨wp,within,real,ind,soft,?_⟩
  intro trial field
  have bought(i:V): ∃(c:Poly (Marks V))(M:Support ((C).side f p) → Config G ((C).side f p) → Poly (Marks V)),
      c.part (Marks V).quiet=0 ∧ Poly.price μ c≤(Fintype.card V:ℝ)*(μ i*a i) ∧
      (∀Z,Burns o Z (M Z) P.p.threshold) ∧ Towed μ id M P.p.B (P.p.supportExponent-1) (μ i*a i) ∧
      ∀U,Poly.send ((Marks V).fire i) (field i U)=c+∑Z,M Z U:=by
    by_cases yes:i∈trial
    · obtain ⟨c,M,cq,cp,loc,paid,split⟩:=WilsonMeasuredPublicEntranceTrialTariff.original Y i x wY μ payment mp
        (by rw [alpha];norm_num) bounded
      have smaller:μ i/wY i*1≤μ i*a i:=by
        rw [mul_one,div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (old i)) (mp i).le
      exact ⟨c,M,cq,cp.trans (mul_le_mul_of_nonneg_left smaller (Nat.cast_nonneg _)),loc,
        paid.shrink le_rfl smaller mp,fun U=>by simpa only [field,if_pos yes] using split U⟩
    · obtain ⟨c,M,cq,cp,loc,paid,split⟩:=WilsonSeparatedPrefixCanonicalSoft.original (J:=Marks V) R live (ref i) o i (q i) (fit i) μ mp
        (fee i) (by rw [alpha];norm_num)
      have smaller: rent R N p f (d i) o i (q i).x μ (P.p.supportExponent-1)+cost P.p*(μ i*B i)≤μ i*a i:=
        (earned i N p live (ref i) fixed o i (q i).x μ (mp i).le (B i) (bn i)).trans
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (inv_nonneg.mpr (payment i).le)) (mp i).le)
      exact ⟨c,M,cq,cp.trans (mul_le_mul_of_nonneg_left smaller (Nat.cast_nonneg _)),loc,
        paid.shrink le_rfl smaller mp,fun U=>by simpa only [field,if_neg yes] using split U⟩
  choose c M quiet costs localFields charge split using bought
  exact ⟨c,M,quiet,costs,localFields,charge,split⟩

end YM.Integration.WilsonMeasuredPublicEntranceHybridSeats
end
