import YM.Integration.WilsonSeparatedPrefixCanonicalWithdrawal
import YM.Integration.WilsonSeparatedPrefixCanonicalWallet
import YM.Integration.WilsonSeparatedPrefixCanonicalSoft
import YM.Integration.WilsonSeparatedPrefixCanonicalForced

/-! Full masked singletons mounted with their own coordinates and the actual
once-divided hard allowances on one original physical report. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalMounted
open Function Filter Finset Lattice RG Wilson Source Labels Marker Push QuadraticLocal MergeProof MergeProof.Accent
open GridApprox.Nil Push.Local PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extra.Histories
open WilsonOriginalStarPrimaryCatalog WilsonRetainedMarkedInletRegular Trace.Physical.GermGraph
open Lodestar Ac
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){V:Type}[DecidableEq V][Fintype V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

def salary(d:V → ℕ)(f p:ℕ)(q:∀v,Coefficient ((C).labels.level (d v)) ((C).side f p))
    (B:V → ℝ)(v:V):ℝ:=(H f)^6*(((C).labels.level (d v)).coeffSize (q v).x)+(H f)^2*B v

theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (book:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ f:ℕ in atTop,∀N p:ℕ,f≤N → ((A).params f).supportExponent=100 →
    ∀(o:V → Site ((C).side f p))(q:∀v,Coefficient ((C).labels.level (d v)) ((C).side f p))(w₀ B:V → ℝ),
    let P:=(C).path.rep N p f
    let a:=salary R d f p q B
    let w:=WilsonSeparatedPrefixCanonicalWallet.seat w₀ a B
    let μ:=fun v=>w v^2
    let m:=fun v=>μ v*a v
    let e:=P.p.supportExponent-1
    let κ:=LocalComparison.forcedDivisor (C) f
    (∀v,0<w₀ v) → (∀v,(C).ref (d v)≤f) → (∀v,(q v).Format (o v) (C).params P) →
    (∀v,(q v).remBound (o v) P κ (B v)) →
    (∀v,0<w v) ∧ (∀v,μ v≤w₀ v) ∧ (∀v,(μ v)⁻¹=WilsonSeparatedPrefixCanonicalWallet.debit w₀ a B v) ∧
    5≤P.p.supportExponent ∧ (∑v,m v)≤1/8 ∧ (∑v,μ v*B v)≤1/8 ∧
    ∃(c:V → Poly (Marks V))(M:V → Support ((C).side f p) → Config G ((C).side f p) → Poly (Marks V)),
      (∀v,(c v).part (Marks V).quiet=0) ∧ (∀v,Poly.price μ (c v)≤(Fintype.card V:ℝ)*m v) ∧
      (∀v Z,Burns o Z (M v Z) P.p.threshold) ∧ (∀v,Towed μ id (M v) P.p.B e (m v)) ∧
      (∀v U,Poly.send ((Marks V).fire v) ((q v).exponentialEntry (o v) ((C).localSection (d v)) P U)=c v+∑Z,M v Z U) ∧
      (∀v b,Flow o b (fun U=>Poly.send ((Marks V).fire v) (profile P.activities (q v).forced b U)) P.p.threshold) ∧
      (∀v,Towed μ Prod.fst (fun b U=>Poly.send ((Marks V).fire v) (profile P.activities (q v).forced b U)) P.p.B e (μ v*(κ*B v))) := by
  have allDates:=Filter.eventually_all.mpr (fun v:V=>WilsonSeparatedPrefixCanonicalIncome.original R (d v) simple pace book)
  filter_upwards [allDates] with f fees N p live fixed o q w₀ B P a w μ m e κ positive ref fit pay
  have board:P.p=(A).budget f:=(R.makes.wilson.represents N p f live).vac
  have exactWidth:P.p.supportExponent=100:=by rw [board];exact fixed
  have wide:5≤P.p.supportExponent:=by rw [exactWidth];norm_num
  have bn(v):0≤B v:=rem_nonneg (pay v)
  have an(v):0≤a v:=by
    have coord:0≤((C).labels.level (d v)).coeffSize (q v).x:=by unfold Frame.coeffSize;positivity
    have :=bn v
    change 0≤(H f)^6*(_)+(H f)^2*B v
    positivity
  obtain ⟨wp,thin,inverse,reg,hard⟩:=WilsonSeparatedPrefixCanonicalWallet.original w₀ a B positive an bn
  have mp(v):0<μ v:=pow_pos (wp v) _
  have unit:1≤P.p.supportExponent:=by linarith
  let trueFee(v):=rent R N p f (d v) o v (q v).x μ e+cost P.p*(μ v*B v)
  have cover(v):trueFee v≤ m v:=fees v N p live (ref v) fixed o v (q v).x μ (mp v).le _ (bn v)
  choose c M quiet constant lamps localFee split using fun v=>WilsonSeparatedPrefixCanonicalSoft.original (J:=Marks V) R live (ref v) o v (q v) (fit v) μ mp (pay v) unit
  have forced(v):=(WilsonSeparatedPrefixCanonicalForced.original (J:=Marks V) v (q v) (fit v) μ mp (by linarith) (pay v))
  refine ⟨wp,thin,inverse,wide,reg,hard,c,M,quiet,?_,lamps,?_,split,fun v=>(forced v).2,?_⟩
  · exact fun v=>(constant v).trans (mul_le_mul_of_nonneg_left (cover v) (Nat.cast_nonneg _))
  · exact fun v=>(localFee v).shrink le_rfl (cover v) mp
  · exact fun v=>(forced v).1.shrink (by dsimp [e];linarith) le_rfl mp

end YM.Integration.WilsonSeparatedPrefixCanonicalMounted
