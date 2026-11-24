import YM.Integration.WilsonPointChildWidthHistory
import YM.FormalBulk08.Trellis.Band

/-! The inverse invoice of the genuine fixed-child matrix follows from its
    forward coefficients on the full roster, with each physical engineering
    height kept until after the triangular inversion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildInverseIncome
open YM FormalBulk08 Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Dove Sierra Trellis
open PhysicalNext.Repeat.Legato Next.Foundations Borough
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open WilsonNeutralPointCourse WilsonPointChildFiledSalary WilsonPointChildNormalizedWidth WilsonPointChildWidthPortfolio
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

variable {G:Gauge}{d D:ℕ}

private theorem total {X:Type}(τ:Time X)(F:Frame G d)(E:ℕ)(T:X→Tilework F)
    (rent:∀b s:Letter F,∀l≤E,Soft τ (fun x=>coeff l (T x b s))):
    Soft τ (fun x=>invoice F (T x) E):=by
  apply (soft_coin τ 1).plus
  apply soft_bill
  intro y _
  apply soft_bill
  intro b _
  apply soft_bill
  intro t ht
  have cap:t.1≤E:=by
    have sum:=Finset.HasAntidiagonal.mem_antidiagonal.mp ht
    have h:=y.2.isLt
    omega
  exact (rent b y.1 t.1 cap).radius

structure Date (R:Run G)(k:ℕ) where
  upper:ℕ
  date:ℕ
  prior:k≤date
  live:date<upper
  digit:∀i,Site (R.family.S.block i)

variable (R:Run G)(wood:Primer.Families R.family)(a:hue G)(depth:d<D)(o:Loc G 1)
local notation "A" => R.family.path.levels
local notation "Λ" => RG16.Lambda A
local notation "F" => R.family.labels.level d

def Forward (E:ℕ):Prop:=∀b s:Letter F,∀l≤E,∃c:ℝ,∃v:ℕ,0≤c ∧
  ∀ᶠj:ℕ in atTop,∀N,j<N→∀digit:∀i,Site (R.family.S.block i),
    |coeff l (transfer R wood a depth digit N j b s)| ≤ c*(Λ j)^v

def Weak (E:ℕ):Prop:=∃c:ℝ,∃v:ℕ,1≤c ∧ ∀ᶠj:ℕ in atTop,∀N,j≤N→∀digit:∀i,Site (R.family.S.block i),
    Wallet o F (filed R wood a depth digit N j) 0 E (c*(Λ j)^v)

include o in
theorem original (simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    {E:ℕ}(credit:Forward R wood a depth E):∃c:ℝ,∃v:ℕ,0≤c ∧ ∀ᶠj:ℕ in atTop,
    ∀N,j<N→∀digit:∀i,Site (R.family.S.block i),
      invoice F (transfer R wood a depth digit N j)⁻¹ E ≤ c*(Λ j)^v:=by
  let I:=Letter F×Letter F×Fin (E+1)
  choose c v cn offers using fun q:I=>credit q.1 q.2.1 q.2.2.val (by omega)
  obtain ⟨k,gated⟩:=eventually_atTop.mp
    (((A).fits.deep.eventually_ge_atTop d).and (Filter.eventually_all.mpr offers))
  let X:=Date R k
  have one (j:ℕ):1≤Λ j:=(le_max_left ..).trans (WilsonPointChildWidthPurchase.prices R granted j).2.2.2
  let τ:Time X:=⟨fun x=>Λ x.date,fun x=>one x.date⟩
  let T (x:X):=transfer R wood a depth x.digit x.upper x.date
  let h (x:X)(b:Letter F):=Grail.heightK (R.family.S.block x.date) d (Pose.weight F b)
  have shape (x:X):Found (slots F) (Pose.weight F) (T x) (h x):=by
    exact down (WilsonNeutralPointCourse.received R wood a depth x.digit x.upper x.date simple o x.live
      ((gated x.date x.prior).1.trans ((A).fits.mono (Nat.le_succ _)))).1
  have diag (b:Letter F):Soft τ (fun x=>(h x b)⁻¹):=by
    apply (soft_coin τ 1).below
    intro x
    obtain ⟨i,N,kj,live,digit⟩:=x
    change |(Grail.heightK (R.family.S.block N) d (Pose.weight F b))⁻¹|≤|1|
    rw [Grail.heightK_of_le _ (Pose.weightFits ..),abs_one]
    have L1:1≤((R.family.S.block N).val:ℝ):=by exact_mod_cast (Nat.le_trans (by decide:1≤2) (Elm.growL (A) N))
    have p:1≤((R.family.S.block N).val:ℝ)^(d-Pose.weight F b):=one_le_pow₀ L1
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans p))]
    exact inv_le_one_of_one_le₀ p
  have priced (b s:Letter F):Priced τ (fun _=>0) (fun x=>T x b s) (fun x=>T x b s) E:=by
    intro l cap
    let m:I:=(b,s,⟨l,by omega⟩)
    apply Pact.constant
    exact ⟨c m,v m,cn m,fun x=>(gated x.date x.prior).2 m x.upper x.live x.digit⟩
  have inverse:=prize_back shape shape diag priced
  obtain ⟨g,w,gn,owed⟩:=total τ F E (fun x=>(T x)⁻¹) (fun b s l cap=>(inverse b s l cap).left)
  refine ⟨g,w,gn,?_⟩
  filter_upwards [eventually_ge_atTop k] with j kj
  intro N live digit
  exact (le_abs_self _).trans (owed ⟨N,j,kj,live,digit⟩)

theorem income (simple:G.Simple){orders:ℕ→ℕ}(granted:WilsonWindowFormalPurchase.Canonical orders R.kit)
    {E:ℕ}(table:Weak R wood a depth o E)(matrix:Forward R wood a depth E):
    WilsonPointChildWidthHistory.Income R wood a depth o E:=by
  obtain ⟨A₀,p,A1,at₁⟩:=table
  obtain ⟨g,q,gn,at₂⟩:=original R wood a depth o simple granted matrix
  let M:=max A₀ g
  let v:=max p q
  refine ⟨M,v,A1.trans (le_max_left ..),?_⟩
  filter_upwards [at₁,at₂] with j t₁ t₂
  have one:1≤Λ j:=(le_max_left ..).trans (WilsonPointChildWidthPurchase.prices R granted j).2.2.2
  have rise {C:ℝ}{m:ℕ}(C0:0≤C)(CM:C≤M)(mv:m≤v):C*(Λ j)^m≤M*(Λ j)^v:=
    mul_le_mul CM (pow_le_pow_right₀ one mv) (pow_nonneg (zero_le_one.trans one) _) (C0.trans CM)
  exact ⟨fun N live digit=>mono (t₁ N live digit)
    (rise (zero_le_one.trans A1) (le_max_left ..) (le_max_left ..)),
    fun N live digit=>(t₂ N live digit).trans (rise gn (le_max_right ..) (le_max_right ..))⟩

end YM.Integration.WilsonPointChildInverseIncome
