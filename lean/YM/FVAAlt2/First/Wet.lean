import YM.FVAAlt2.First.Signed
import YM.FVAAlt2.Shop.Lobby
/-! Lsup at a vs. 1, at all powers. Preservation tally. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Chart MS.Native.Draft MS.Menus MS.Local.Physical MS.Landau MS.Landau.Detect MS.Lifting MS.Tone MS.Momentum
open MS.Book MS.Book.Convolve MS.Native.Paint MS.Native.Wilsonian MS.Plane MS.Logarithm
open Pert Pert.Orb SchemeRG11 SchemeRG11.Atoll SchemeRG11.Haze SchemeRG11.Pile SchemeRG11.Sway SchemeRG11.Sway.Lam
open MvPolynomial (X IsWeightedHomogeneous)
open PowerSeries (C coeff)
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius PowerSeries Classical Matrix
variable {G: Gauge}{d k:ℕ}{F: Frames G}{n:Side}{p q:pLabel G}{B: Deck G} {i:Glyph B d}
local notation "Φ"=> Dot G Cover
local notation "Qx"=> MvPolynomial.X
local notation "CZ"=> PowerSeries ℂ
variable (o:Site n)(ε:ℝ)
lemma tensor_fare (i:Key G)(U:Config G n): Bare.tensorJet ε U o i.1= pad ε i • Bare.tensorJet 1 U o i.1:=by
 unfold Bare.tensorJet Bare.oval Bare.rawJet; simp only [map_smul, _root_.one_zpow, one_smul,pad_eq ε i]; rw [ ← Finset.smul_sum,smul_comm (pad ε i) ]
lemma layout_cost {S:Type*} [NormedAddCommGroup S][NormedSpace ℝ S] (f:S→L[ℝ]Potential G n)(i:Key G): layout f o ε i=(pad ε i:ℂ) • layout f o 1 i:=by
 let m(h:ℝ):=Bare.datum h o i ∘ f
 have he : m ε=(fun x=> (pad ε i:ℂ))*m 1:= by
    funext a; change Complex.ofReal ((Labels.axes G i.1).coord i.2 (Bare.tensorJet ε (positiveLinks (f a)) o i.1))= (pad ε i:ℂ)* Complex.ofReal ((Labels.axes G i.1).coord i.2 (Bare.tensorJet 1 (positiveLinks (f a)) o i.1)); rw [← Complex.ofReal_mul]; apply congr_arg Complex.ofReal; change (Labels.axes G i.1).coord i.2 (Bare.tensorJet ε (positiveLinks (f a)) o i.1)=_; rw [tensor_fare o ε i,map_smul]
    rfl
 have hc (v q:S→ℂ)(a:ℂ)(h:v=(fun _=>(a:ℂ))*q)(hv:ContDiffAt ℝ ∞ q 0) (s:S)(i:ℕ): PowerSeries.coeff i (ChartC v s)= a • PowerSeries.coeff i (ChartC q s):=by rw [h,show (fun _=>a)*q=(fun x=>a*q x) from rfl, chart_mul contDiffAt_const hv,chart_const,Pi.mul_apply]; exact PowerSeries.coeff_C_mul ..
 funext t; ext1 j; simp only [layout,Pi.smul_apply,PowerSeries.coeff_smul,PowerSeries.coeff_mk]; exact hc (m ε) (m 1) (pad ε i) he (datum_slick f o 1 i) t (j+1)
lemma leaf_scaled (i:Key G) : layout (E:=Land G n) (g0 G n) o ε i= (pad ε i:ℂ) • layout (E:=Land G n) (g0 G n) o 1 i:= by have he:=layout_cost (S:=Land G n) o ε (g0 G n) i; with_reducible exact he
lemma tabs_scalar (p:Pol G)(c:ℂ): Lsup o ε (c • p) = c • Lsup o ε p:= by funext i; unfold Lsup tabs; simp only [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval₂Hom_C, Pi.smul_apply, PowerSeries.smul_eq_C_mul]
lemma tabs_op (p q:Pol G): Lsup o ε (p*q)= Lsup o ε p * Lsup o ε q:= funext fun _=> map_mul (MvPolynomial.eval₂Hom _ _) p q
lemma tabs_scal (p:pLabel G): Lsup o 1 ( realCast (etude ε p) ) = Lsup o ε (realCast p):=by
 induction p using MvPolynomial.induction_on with
 | C c=> unfold etude realCast Lsup tabs; simp only [Haze.vary_C,MvPolynomial.map_C,MvPolynomial.eval₂Hom_C]
 | add a b ha hb=>
    have hε(h:ℝ)(p q: pLabel G): Lsup o h (realCast (p+q))= Lsup o h (realCast p)+Lsup o h (realCast q):=by unfold realCast; rw [map_add]; exact funext fun t=>map_add (MvPolynomial.eval₂Hom ..) _ _
    rw [show etude ε (a+b)=etude ε a+etude ε b from map_add _ a b,hε,hε,ha,hb] -- unfold vary? implicit
 | mul_X p i hp=>
    have hε(h:ℝ)(p q:pLabel G): Lsup o h (realCast (p*q))= Lsup o h (realCast p)*Lsup o h (realCast q):=by unfold realCast; rw [map_mul]; exact tabs_op ..
    rw [show etude ε (p*X i)= etude ε p*etude ε (X i) from map_mul ..,hε,hε,hp, uniformX, realCast_scalar, tabs_scalar, show realCast (X i)=X i from MvPolynomial.map_X ..]; congr 1; unfold Lsup tabs; simp_rw [MvPolynomial.eval₂Hom_X']; exact ( leaf_scaled o ε i ).symm
lemma sloped (hp:IsWeightedHomogeneous Labels.generation p d): Lsup o ε (dream ε (realCast p))=( ((ε:ℂ)⁻¹)^d ) • Lsup o 1 (dream 1 (realCast p)):=by
 rw [utc,utc, ← tabs_scal,show etude ε ((winds G ε).heat p)=_ from ( show _=(winds G 1).heat (etude ε p) from ?_),Pile.programDeg _ _ hp,map_smul,realCast_scalar,tabs_scalar]; rotate_left
 · unfold winds etude; rw [ Dose.night, Pile.sloped ]
 simp only [Complex.ofReal_pow,Complex.ofReal_inv]
lemma dilation (hp:Orbis p d k)(q: Pol G)(he:q=realCast p): Lsup o ε (dream ε q)=( C (((ε:ℂ)⁻¹)^d) : CZ ) • Lsup o 1 (dream 1 q):=by
 rw [he,sloped o ε (weightL hp)]; exact funext fun u=> PowerSeries.smul_eq_C_mul _ _
end YM.FVAAlt2.Pairing
