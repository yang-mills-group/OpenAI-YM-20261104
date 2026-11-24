import YM.Integration.WilsonPositionProgramNormalizedAmplitude
import YM.Integration.WilsonPositionProgramReflectedRead
import YM.Integration.WilsonMaxwellThermometerReflectedFirstPrice

/-! The two original independently normalized reflected first readings, at
their own horizons four and six, and their true W/V comparator. The additive
first-incidence residual is retained on those two signed entries. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerIndependentReflection
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops Labels XSpace XSpace.Cirrus XSpace.Normalize Maxwell Table.Pairing
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonMaxwellThermometerLowerPointGram (occupied)
open WilsonMaxwellThermometerLowerGramPrice (token reassemble)
open WilsonMaxwellThermometerReflectedIncidence (site mass Gram)
open WilsonMaxwellThermometerReflectedFirstPrice (filed)
open scoped Classical BigOperators
variable {G:Gauge} {k u D e:ℕ} (R:Run G)

def degrees:Fin 2→ℕ:=![4,6]
def cut (l d:ℕ):Fin 2→ℕ:=![l,d]
abbrev panel {l d:ℕ}(h4:4<l)(h6:6<d):Fin 2→SealR G:=
  WilsonMarkedIndependentNormalizedElection.deck (G:=G) degrees (cut l d)
    (by intro i;fin_cases i <;> first | exact h4 | exact h6)

def magnitude {Q:Fin 2→SealR G}(t:ℕ)(E:Herit Q)(w:Fin 2→ℝ)(A:ℝ):ℝ:=
  ∏i,w i*(A*WilsonPositionProgramNormalizedMaster.fee E t i)

/-- Each deletion retains its explicit, independently submitted unit or
other declared comparison field, and every live copy retains the same real
coupling reversion. -/
def posted {Q:Fin 2→SealR G}(E O:Herit Q)(S:Finset (Fin 2)):Herit Q:=
  fun i=>if i∈S then E i else O i

def reading {Q:Fin 2→SealR G}(big:0<D)(φ:Wilt Q)(X:Herit Q)
    (m j N k t:ℕ)(f:Alma ((primes G).F 0)):ℝ:=
  PowerSeries.coeff t (Reports R.family.path.levels R.metals.O ((primes G).T 0) big φ
    (normalized R.family.path.levels R.metals.O Q X m N) m m j N k f)

/-- Sum the real and imaginary source polarizations, properly centered on
their own true ordinary pair and singleton first coefficients at the common
finite h=0 scalar report. -/
def pair (J:Finset (Fin 2)→ℕ→ℝ):ℝ:=
  J univ 1-J {0} 1*J {1} 0-J {0} 0*J {1} 1

private theorem priced (J:Finset (Fin 2)→ℕ→ℝ) (A:Finset (Fin 2)→ℝ)
    (fee:∀S,∀t≤1,‖J S t‖≤A S):
    ‖pair J‖≤A univ+2*(A {0}*A {1}):=by
  have a:=fee {0} 0 (by decide)
  have b:=fee {1} 0 (by decide)
  have x:‖J {0} 1*J {1} 0‖≤A {0}*A {1}:=by
    rw [norm_mul];exact mul_le_mul (fee _ 1 le_rfl) b (norm_nonneg _) ((norm_nonneg _).trans a)
  have y:‖J {0} 0*J {1} 1‖≤A {0}*A {1}:=by
    rw [norm_mul];exact mul_le_mul a (fee _ 1 le_rfl) (norm_nonneg _) ((norm_nonneg _).trans a)
  calc
    _≤‖J univ 1-J {0} 1*J {1} 0‖+‖J {0} 0*J {1} 1‖:=norm_sub_le ..
    _≤(A univ+A {0}*A {1})+A {0}*A {1}:=
      add_le_add ((norm_sub_le ..).trans (add_le_add (fee _ 1 le_rfl) x)) y
    _=_:=by ring

/-- A paid numerical two-slot h=0 response. The independent regulator(s)
behind the genuine native cutoff N stay independent from the public M. -/
theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(he:1≤e){l d:ℕ}(h4:4<l)(h6:6<d)
    (cap:capP (panel (G:=G) h4 h6)≤k)
    (a:Axis)(x:E4)(hx:0<x a)(W:Initialize G)(V:Normalize.Store G)(b:Sec G 6):
    let Q:=panel (G:=G) h4 h6
    let L:=R.family.path.levels
    ∃B:Bulb (site x) a,∃φ:Wilt Q,∃w:Fin 2→ℝ,
      WilsonPositionProgramReflectedRead.reading Q a φ=mass a x B ∧
      (∫p:WilsonMaxwellThermometerReflectedIncidence.Pair,
        WilsonPositionProgramReflectedRead.reading Q a φ p)=1 ∧
      ∃C A C₀ B₀:ℝ, ∃k₀ k₁:ℕ, 0<C ∧ 0≤A ∧
      (∀ᶠ Z:ℝ in atTop,Bough Q φ 1 Z w) ∧ ∀ᶠ M in Front,∀c∈M.Box,
      ∀ᶠ j:ℕ in atTop, ∀ m : ℕ, j ≤ m → ∀ N : ℕ, m ≤ N → ∀f:Alma ((primes G).F 0),
      ∀E:Bool→Herit Q,∀O:Herit Q,∀Z:ℝ,Compar L.S (zz L) j m≤Z → Bough Q φ (paceT L.S m m) Z w →
      let array (s:Bool)(S:Finset (Fin 2))(t:ℕ):=reading R big φ (posted (E s) O S) m j N k t f
      let sign (s:Bool):ℂ:=pair (array s)
      let funds (s:Bool)(S:Finset (Fin 2)):=C₀*Z^k₀*magnitude e (posted (E s) O S) w (B₀*(zz L m)^k₁)
      ∀z:occupied G a x,∀fee:ℝ,
      ‖(sign-filed a x W V B b M c)-reassemble a x (Gram a x W V B M c) z‖≤fee →
      ‖token a x z‖≤C*((∑s:Bool,(funds s univ+2*(funds s {0}*funds s {1})))+A+fee):=by
  intro Q L
  obtain ⟨B,C,A,hC,hA,due⟩:=WilsonMaxwellThermometerReflectedFirstPrice.original a x W V hx b
  obtain ⟨φ,w,afford,same,one⟩:=WilsonPositionProgramReflectedRead.original Q a x B 1
  obtain ⟨C₀,B₀,_,_,k₀,k₁,main⟩:=WilsonPositionProgramNormalizedAmplitude.original R simple v funded big rails
    degrees (cut l d) (by intro i;fin_cases i <;> first | exact h4 | exact h6) cap
  refine ⟨B,φ,w,same,one,C,A,C₀,B₀,k₀,k₁,hC,hA,afford,?_⟩
  filter_upwards [due] with M measure
  intro c hc
  filter_upwards [main] with j pay
  intro m late N upper f E O Z hz booked array sign funds z fee current
  have output:=measure c hc z sign fee current
  have band (s:Bool)(S:Finset (Fin 2))(t:ℕ)(ht:t≤1):‖array s S t‖≤funds s S:=
    (pay (posted (E s) O S) m m late le_rfl φ w Z hz booked t (ht.trans he) f N upper).1
  have normed (s:Bool):‖sign s‖≤funds s univ+2*(funds s {0}*funds s {1}):=by
    simpa only [sign,Complex.norm_real] using priced (array s) (funds s) (band s)
  let J (s:Bool):=funds s univ+2*(funds s {0}*funds s {1})
  have pos (s:Bool):0≤J s:=(norm_nonneg _).trans (normed s)
  have total:‖sign‖≤∑s,J s:=(pi_norm_le_iff_of_nonneg (sum_nonneg fun s _=>pos s)).mpr
    (fun s=>(normed s).trans (single_le_sum (f:=J) (fun i _=>pos i) (mem_univ s)))
  exact output.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add total le_rfl) le_rfl) hC.le)

end YM.Integration.WilsonMaxwellThermometerIndependentReflection
