import YM.Integration.WilsonRegisteredAffineRows
import YM.Integration.WilsonRegisteredAngularPair

/-! The charged forest segment requires a larger physical halo than the
primary stencil. Its genuine one-face reflection purchase pays the entire
halo under the original Wilson marginal, before all periods and sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineHalo
open Filter Finset Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open MeasureTheory Push.AbsoluteSums.Animals WilsonReportingForestAngularFare
open WilsonReportingForestAngularReflection
open scoped Classical
variable {G:Gauge} (R:Run G)
local notation "A"=>R.family.path.levels
local notation "β"=>R.family.path.levels.clock.hatBeta

def radius (p base k:ℕ):ℕ :=
  let B:=(A).clock.coverSize k
  base+WilsonDegreeFourInheritedRange.height R p k*(4*B+2)+2*B

/-- In particular this one exponent need not grow with the perturbative
order or with the size of a fixed primary footprint. -/
theorem count (simple:G.Simple) (p base:ℕ) :
    ∀ᶠ k:ℕ in atTop,∀ per (o:Site (R.family.side k per)),
    ((WilsonPhysicalHistoryKioskPlaquettes.faces (radius R p base k) o).card:ℝ)  ≤  β k := by
  let D:ℝ:=base+10*((p:ℝ)+3)+4
  let C:=625*((2*D+1)^4)*(Fintype.card PlaqAxes:ℝ)
  have dp:0<D:=by dsimp [D];positivity
  have cp:0<C:=by dsimp [C];positivity
  have grow:=Next.Rank.Station.hat_rate (A) simple
  have small:= (Real.isLittleO_pow_log_id_atTop (n:=12)).bound (inv_pos.mpr cp)
  filter_upwards [grow.eventually small,(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop 1] with k budget one
  intro per o
  let s:=Real.log (β k)
  let B:=(A).clock.coverSize k
  let b:=WilsonDegreeFourInheritedRange.height R p k
  let H:=radius R p base k
  have sp:1 ≤ s:=one
  have non:0 ≤ s:=zero_le_one.trans sp
  have sp2:1 ≤ s^2:=one_le_pow₀ sp
  have sp3:1 ≤ s^3:=one_le_pow₀ sp
  have grow23:s^2 ≤ s^3:=pow_le_pow_right₀ sp (by decide)
  have HB:(B:ℝ) ≤ 2*s^2 := ((Nat.ceil_lt_add_one (sq_nonneg s)).le).trans (by linarith only [sp2])
  have hb:(b:ℝ) ≤ ((p:ℝ)+3)*s:=by
    have tmp: (b:ℝ) ≤ (((p+2:ℕ):ℝ)*s)+1:=(Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) non)).le
    push_cast at tmp;linarith only [tmp,sp]
  have radiusFit:(H:ℝ) ≤ D*s^3:=by
    have corner:4*(B:ℝ)+2 ≤ 10*s^2:=by linarith only [HB,sp2]
    have rest:2*(B:ℝ) ≤ 4*s^3:=by linarith only [HB,grow23]
    have baseFit:(base:ℝ) ≤ base*s^3:=le_mul_of_one_le_right (Nat.cast_nonneg _) sp3
    change ((base+b*(4*B+2)+2*B:ℕ):ℝ) ≤ _
    push_cast
    calc
      _  ≤  (base:ℝ)*s^3+(((p:ℝ)+3)*s)*(10*s^2)+4*s^3:=
        add_le_add (add_le_add baseFit (mul_le_mul hb corner (by positivity) (by positivity))) rest
      _=D*s^3:=by dsimp only [D];ring
  have ball:((ballCost H:ℕ):ℝ) ≤ (2*D+1)^4*s^12:=by
    change (((H+H+1)^4:ℕ):ℝ) ≤ _
    push_cast
    calc
      _  ≤  ((2*D+1)*s^3)^4 := pow_le_pow_left₀ (by positivity) (by linarith only [radiusFit,sp3]) 4
      _ = _:=by ring
  have paper:((WilsonPhysicalHistoryKioskPlaquettes.faces H o).card:ℝ)  ≤ 
      625*(ballCost H:ℕ)*(Fintype.card PlaqAxes:ℝ):=by exact_mod_cast WilsonPhysicalHistoryKioskPlaquettes.count H o
  have cash:s^12  ≤  C⁻¹*β k:=by
    have bp:0 ≤ β k:=zero_le_one.trans ((A).fits.delayed k).le
    change ‖s^12‖ ≤ C⁻¹*‖β k‖ at budget
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg non 12),abs_of_nonneg bp] using budget
  calc
    _  ≤  _:=paper
    _  ≤  625*((2*D+1)^4*s^12)*(Fintype.card PlaqAxes:ℝ):=by gcongr
    _ = C*s^12:=by dsimp only [C];ring
    _  ≤  C*(C⁻¹*β k):=mul_le_mul_of_nonneg_left cash cp.le
    _ = _:=by rw [←mul_assoc,mul_inv_cancel₀ cp.ne',one_mul]

/-- The union of both actual halo rejection events, including both sites and
all their retained supports, under the original positive measure. -/
theorem purchased (simple:G.Simple) (gate:posted R) (p base d q:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N per (_live:m<N) (o:Fin 2→Site (R.family.side (m+1) per)),
    let k:=m+1
    let bad:=⋃i,(House.chilly (G:=G) (WilsonPhysicalHistoryKioskPlaquettes.faces (radius R p base k) (o i)) (angularCut (β k)))ᶜ
    β k^d*(scene R.family.path N per k).real bad  ≤  ε*Pert.Asymptotics.regulatorRun R.family N per k^q := by
  let n:=d+1
  let l:=ε/2
  have lp:0<l:=div_pos he (by norm_num)
  have pay:=WilsonReportingForestAngularCurrency.currency R simple n q lp
  have invoice:=WilsonReportingForestAngularReflection.original R simple gate (n+q+1)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (count R simple p base),pay,invoice] with m countHere cash billed
  intro N per live o k bad
  let a:=((β k)⁻¹)^(n+q+1)
  have bp:0 ≤ β k:=zero_le_one.trans ((A).fits.delayed k).le
  have pos:0 ≤ a:=pow_nonneg (inv_nonneg.mpr bp) _
  let μ:=scene R.family.path N per k
  letI : IsProbabilityMeasure (scene R.family.path N per k):=probability R.makes.wilson live
  let J i:=WilsonPhysicalHistoryKioskPlaquettes.faces (radius R p base k) (o i)
  have each (i:Fin 2):μ.real (House.chilly (J i) (angularCut (β k)))ᶜ  ≤  (β k)*a :=
    (House.cool_miss a (billed N per live) (J i)).trans (mul_le_mul_of_nonneg_right (countHere per (o i)) pos)
  have common:μ.real bad ≤ 2*((β k)*a):=calc
    _ ≤ ∑i:Fin 2, μ.real (House.chilly (J i) (angularCut (β k)))ᶜ:=measureReal_iUnion_fintype_le _
    _ ≤ ∑_:Fin 2,(β k)*a:=sum_le_sum (fun i _=>each i)
    _=_:=by simp
  calc
    _  ≤  β k^d*(2*((β k)*a)):=mul_le_mul_of_nonneg_left common (pow_nonneg bp _)
    _ = 2*((β k)^n*a):=by dsimp only [n];rw [pow_succ];ring
    _  ≤  2*(l*Pert.Asymptotics.regulatorRun R.family N per k^q):=
      mul_le_mul_of_nonneg_left (cash N live per) (by norm_num)
    _ = _:=by dsimp only [l];ring

end YM.Integration.WilsonRegisteredAffineHalo
end
