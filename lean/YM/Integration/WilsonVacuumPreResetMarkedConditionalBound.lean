import YM.Integration.WilsonVacuumPreResetMarkedLogBound
import YM.Integration.WilsonVacuumPreResetFiniteHeatWindow
import YM.Integration.WilsonMarkedIndependentFiniteHeat
import YM.Integration.WilsonMarkedIndependentEnrolledHeatWallet

/-! The actual original affine conditional bounds every required
intermediate heat coefficient in the norm of an arbitrary occupied tensor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedConditionalBound
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetFiniteHeatFinance
open scoped Classical BigOperators
variable {G:Gauge}{e:ℕ}{C:Arch G}

theorem selected (p:ScrollV e C)(A:ℝ)(l r:ℕ)(npos:0≤A)
    (old:∀i ≤ e,∀v ≤ horizon e (r+2*l),∀x,|casePW p.wheel C.R p.cone p.W' i v x|≤A)
    (D:PChart G (p.n*C.P.L))(small:∀i≤e,∀v≤horizon e (r+2*l),∀x,|D i v x|≤1)
    (t:ℝ)(unit:|t|≤1)(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V]
    (T:Pal V (Woods G (p.n*C.P.L)))(a:ℝ)(hot:0<a)
    (marked:Bounded e (horizon e (r+2*l)) T a) :
    ∀h≤l+3*e,Bounded e r (srShade p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•D) T h)
      (a*(fee p A (r+2*l))^(20*3^(l+3*e))):=by
  intro h active i hi s hs x
  let J:=horizon e (r+2*l)
  let B:=fee p A (r+2*l)
  obtain ⟨base,width,many,mass,shifts,input⟩:=inputs p A (r+2*l) npos old D small t unit
  let K:=fillSlots (Woods G p.n) (FreeResolvent.covariance G p.wheel p.shadow p.H)
  let V₀:=casePW p.wheel C.R p.cone (p.W'+t•D)
  let z:=srShade p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•D) T h i s x
  obtain ⟨L,one,read⟩:=exists_dual_vector'' ℝ z
  have norm(v:V):|L v|≤‖v‖:=by
    simpa only [←Real.norm_eq_abs,one_mul] using
      (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right one (norm_nonneg _))
  let Z:ℕ→Gen ℝ (Joint G (p.n*C.P.L) p.n):=fun j=>cloaks L.toLinearMap (srCold T p.cone j)
  have row(j:ℕ)(hj:j≤e)(v:ℕ)(hv:v≤J)(y):|Z j v y|≤a*B:=by
    have inside(u):|cloaks L.toLinearMap (T j) v u|≤a:=(norm (T j v u)).trans (marked j hj v hv u)
    have applyAt:=application (camber G p.cone) (cloaks L.toLinearMap (T j)) v C.mass a
      (zero_le_one.trans C.book) hot.le (shifted p) inside y
    have eq:Z j v y=fade (camber G p.cone) (cloaks L.toLinearMap (T j)) v y:=
      congrFun (congrFun (cloak_fade L.toLinearMap (camber G p.cone) (T j)) v) y
    rw [eq]
    exact applyAt.trans (by simpa only [mul_comm a] using mul_le_mul_of_nonneg_right (shifts v hv) hot.le)
  have bound:=WilsonMarkedIndependentFiniteHeat.original J e (by dsimp only [J,horizon];omega)
    K V₀ Z B a base hot width many (fun u y=>(noise p u y).trans mass) input row
  have converted:L z=bul K (abr K V₀) Z h i s x:=
    congrFun (congrFun (cloak_bul L.toLinearMap K (abr K V₀) (srCold T p.cone) h i) s) x
  have result:=bound h i s hi (by dsimp only [J,horizon];omega) x
  rw [←converted,show L z=‖z‖ from read,abs_of_nonneg (norm_nonneg _)] at result
  exact result.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by dsimp only [B];linarith)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) active))) hot.le)

end YM.Integration.WilsonVacuumPreResetMarkedConditionalBound
end
