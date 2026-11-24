import YM.Integration.WilsonRegisteredRectangleLaw

/-! Four separate signed factors of the genuine compact two-region determinant.
Only the numbered old spring enters its geometric exponential difference. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFactors
open Function Filter MeasureTheory Lattice RG Wilson OriginalMarkedRunAction
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Classical
variable {X Y:Type*}
def diagonal (f:X×Y→ℝ)(x y:X×Y):ℝ:=f x*f y
def across (f:X×Y→ℝ)(x y:X×Y):ℝ:=f (y.1,x.2)*f (x.1,y.2)
def determinant (f:X×Y→ℝ)(x y:X×Y):ℝ:=diagonal f x y-across f x y
def difference (f:X×Y→ℝ)(x y:X×Y):ℝ:=f x+f y-f (y.1,x.2)-f (x.1,y.2)

theorem exponential (q:X×Y→ℝ)(c:ℝ)(x y:X×Y):determinant (fun z=>Real.exp (c-q z)) x y=
    across (fun z=>Real.exp (c-q z)) x y*(Real.exp (-difference q x y)-1):=by
  unfold determinant diagonal across difference
  rw [←Real.exp_add,←Real.exp_add]
  rw [mul_sub,mul_one,←Real.exp_add]
  congr 2
  ring

variable {G:Gauge}(R:Run G){m N per:ℕ}
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "P" => R.family.path.rep N per (m+1)
local notation "β" => R.family.path.β N per (m+1)
local notation "step" => R.family.path.levels.clock.op m per

set_option backward.isDefEq.respectTransparency false in
theorem original (r:ℕ)(Z:SeriesA G)(σ C:ℝ)(S T:Support (R.family.side (m+1) per))(ext:fine)(W:coarse)(x y:fine×fine):
    let U:=WilsonRegisteredRectangleLaw.chart S T ext
    let k (z:fine×fine):=(step).density β (U z) W
    let h (z:fine×fine):=(P).activities.gas (P).p (U z)
    let q (z:fine×fine):=(P).path.inChannels (P).clip (P).p β (U z)
    let s (z:fine×fine):=∑z₀:Site (R.family.side (m+1) per),maskedSpringAt R N per (m+1) r Z σ C (regulatorRun R.family N per (m+1)) z₀ (U z)
    let b (z:fine×fine):=Real.exp ((P).scalar-q z)
    let a (z:fine×fine):=Real.exp (-s z)
    let p:=WilsonRegisteredRectangleLaw.weight R (N:=N) (r:=r) Z σ C S T ext W
    WilsonRegisteredRectangleMoment.minor p x y=
      ((diagonal (fun z=>k z*b z*a z) x y*determinant h x y+
        across h x y*
          (diagonal (fun z=>k z*b z) x y*across a x y*(Real.exp (-difference s x y)-1)+
            across a x y*(diagonal k x y*across b x y*(Real.exp (-difference q x y)-1)+
              across b x y*determinant k x y)):ℝ):ℂ):=by
  intro U k h q s b a p
  have old(z:fine×fine):p z=((k z*b z*a z*h z:ℝ):ℂ):=by
    change ((k z*(Real.exp ((P).scalar-(q z+s z))*h z):ℝ):ℂ)=_
    rw [show (P).scalar-(q z+s z)=((P).scalar-q z)+(-s z) by ring,Real.exp_add]
    dsimp only [b,a];push_cast;ring
  have sb:determinant b x y=across b x y*(Real.exp (-difference q x y)-1):=exponential q (P).scalar x y
  have sa:determinant a x y=across a x y*(Real.exp (-difference s x y)-1):=by
    simpa only [zero_sub] using exponential s 0 x y
  rw [mul_assoc (diagonal (fun z=>k z*b z) x y) (across a x y),←sa,
    mul_assoc (diagonal k x y) (across b x y),←sb]
  unfold WilsonRegisteredRectangleMoment.minor
  rw [old,old,old,old]
  push_cast
  dsimp only [determinant,diagonal,across]
  push_cast;ring
end YM.Integration.WilsonRegisteredRectangleFactors
