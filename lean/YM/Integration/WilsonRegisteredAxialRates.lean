import YM.Integration.WilsonRegisteredLogFare
import YM.Integration.WilsonRegisteredAffineHalo

/-! A genuine moving local axial box charge prior to every regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialRates
open Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonRegisteredAffineHalo WilsonRegisteredWidthCurrency WilsonReportingForestAngularReflection
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta
def factor (p base:ℕ):ℝ:=(base:ℝ)+10*((p:ℝ)+3)+4

theorem geometry (p base k:ℕ) (one:1 ≤ Real.log (β k)):
    (radius R p base k:ℝ) ≤ factor p base*(Real.log (β k))^3:=by
  let D:=factor p base
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
      _=D*s^3:=by dsimp only [D,factor];ring
  exact radiusFit

def amplitude (J:Voice G) (H N per k:ℕ):ℝ:=
  256*J.C*(H:ℝ)*(Fintype.card PlaqAxes)*WilsonRegisteredAffineSource.width R N per k

theorem paid (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (p base d:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (_live:m+1 ≤ N),
      let k:=m+1
      let H:=radius R p base k
      let r:=amplitude R J H N per k
      let s:=Real.log (β k)
      r*((A).params k).columns*s^d ≤ ε ∧ r*s^d ≤ ε:=by
  let C:=512*J.C*factor p base*(Fintype.card PlaqAxes)
  have jp:0<J.C:=zero_lt_one.trans_le clear.cost
  have fp:0<factor p base:=by unfold factor;positivity
  have cp:0<C:=by dsimp only [C];positivity
  have small:0<ε/C:=div_pos he cp
  have logs:=(Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)).eventually_ge_atTop 1
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (logarithmic R simple (d+4) small),
    (tendsto_add_atTop_nat 1).eventually logs,WilsonRegisteredLogFare.column R simple slow] with m cash late column
  intro N per live k H r s
  have sp:1 ≤ s:=late
  have s0:0 ≤ s:=zero_le_one.trans sp
  have cols:0 ≤ ((A).params k).columns:=zero_le_one.trans ((A).params k).columns_ge
  have wp:0 ≤ WilsonRegisteredAffineSource.width R N per k:=(band R N per k live).1
  have hp:(H:ℝ) ≤ factor p base*s^3:=geometry R p base k sp
  have paid:=cash N per live
  have money:C*(WilsonRegisteredAffineSource.width R N per k*s^(d+4)) ≤ ε :=
    calc
      _=C*(s^(d+4)*WilsonRegisteredAffineSource.width R N per k):=by ring
      _ ≤ C*(ε/C):=mul_le_mul_of_nonneg_left paid cp.le
      _=ε:=by field_simp
  have first:r*((A).params k).columns*s^d ≤ C*(WilsonRegisteredAffineSource.width R N per k*s^(d+4)):=by
    calc
      _ ≤ (256*J.C*(factor p base*s^3)*Fintype.card PlaqAxes*
           WilsonRegisteredAffineSource.width R N per k)*(2*s)*s^d:=by dsimp only [r,amplitude];gcongr
      _ = _:=by dsimp only [C];rw [pow_add];ring
  have second:r*s^d ≤ C*(WilsonRegisteredAffineSource.width R N per k*s^(d+4)):=by
    have r0:0 ≤ r:=by dsimp only [r,amplitude];positivity
    calc
      _ ≤ (256*J.C*(factor p base*s^3)*Fintype.card PlaqAxes*WilsonRegisteredAffineSource.width R N per k)*(2*s)*s^d:=by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans sp) _)
        exact (le_mul_of_one_le_right r0 (by linarith only [sp] : 1 ≤ 2*s)).trans
          (mul_le_mul_of_nonneg_right (by dsimp only [r,amplitude];gcongr) (by positivity))
      _ = _:=by dsimp only [C];rw [pow_add];ring
  exact ⟨first.trans money,second.trans money⟩

end YM.Integration.WilsonRegisteredAxialRates
end
