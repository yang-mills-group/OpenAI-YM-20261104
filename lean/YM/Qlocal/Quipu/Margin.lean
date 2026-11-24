import YM.Qlocal.Quipu.Wall
import YM.AllOrder.Response.Thermal
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Wall
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Marker Comparison.RG02.Order Comparison.RG02.Assembly
open AllOrder Fire Response PertExtension PertExtension.Series Radial PositionX.Jet PositionX.Gauss GaussianScore
open scoped Topology ENNReal ContDiff BigOperators Classical
open Finset Turbin
variable {V:Type}[DecidableEq V][Fintype V]{R:Census V} {Z X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
  {σ:Type}[Fintype σ] {k n r :ℕ} (M:(σ→ℝ)→L[ℝ]X) (x:X) (Y:σ→Poly R)
variable [NormedAddCommGroup Z][NormedSpace ℝ Z][FiniteDimensional ℝ Z]
  [MeasurableSpace Z][BorelSpace Z] (μ:Measure Z)[μ.IsAddHaarMeasure]
variable (A: Law Z)(E:X×Z→ℝ)(h:Response.Pledge X Z E)(p:R.Mode)
-- factoring explicit.Mark restore uses lower.Mark.E.Power x
abbrev book (p:R.Mode): Poly R →ₗ[ℝ]ℂ:= { toFun:= fun u=> u.part p
                                          map_add':=fun _ _=>rfl
                                          map_smul':=fun _ _=>rfl }
abbrev pole (M:(σ→ℝ)→L[ℝ]X) (Z:Type)[NormedAddCommGroup Z][NormedSpace ℝ Z]: (σ→ℝ)→L[ℝ] (X×Z):=ContinuousLinearMap.inl ℝ X Z ∘L M
def scaleC (A:Law Z)(g:Z→ℂ)(z:Z) := A.kern z • g z
local notation "X'"=> pole M Z
local notation "G'"=>book p
local notation "K"=>A.kern
def closeout : Z→ℂ:= fun z:Z=> A.kern z • (book p (wall Y (polar (pole M Z) (x,z) E)))
local notation "T"=> closeout M x Y A
local notation "u"=> wall Y ∘ polar M x
include h
lemma price_mar : Integrable (T E p) μ ∧ (∫ z,T E p z ∂μ) =(capital A μ) • G' ((u) (bound A μ E)):= by
 induction h with
 | @core a b ha hb =>
    let F : X×Z→ℝ:= fun p=>a p.1*b p.2; let v:= wall Y (polar M x a); let hV:= granted M x a ha; let B:= G' v
    have hf: T F p= fun z:Z=> (b*K) z • B := by
       ext1 z; rw [closeout, show polar X' _ F=(b z) • polar M x a from funext (fun t=>by unfold polar F; change _*b (z+0)=b z* _; rw [add_zero,mul_comm]; rfl), pours_s _ hV]; rw [map_smul, smul_smul,mul_comm]; rfl
    have hJ:= A.integrable_entry μ hb.invoice hb.smooth.continuous; rw [hf]; refine ⟨Integrable.smul_const hJ B,?_⟩; rw [integral_smul_const]; let c:= A.average μ b; have hz : Response.bound A μ F= c • a:= funext (fun x=> (average_scale A μ (a x) b).trans (mul_comm ..)); rw [hz,Function.comp_apply,← pre_s,pours_s _ hV, map_smul, smul_smul]; refine congrArg (· • B) ?_; let h₀:=capital_pos A μ; rw [show c=_ from (show c=(∫ x, (b*K) x ∂μ)/capital A μ from rfl)]; field_simp
 | @add f g h H hf hg =>
    have he : T (f+g) p=T f p+T g p:= by ext1 z; unfold closeout; rw [← pre_a,pours_a _ (granted X' (x,z) _ h.p) (granted X' (x,z) _ H.p),map_add, smul_add]; rfl
    rw [he] -- remove
    refine ⟨hf.1.add hg.1,?_⟩; simp_rw [Pi.add_apply]; rw [integral_add hf.1 hg.1, hf.2,hg.2]; simp_rw [Function.comp_apply]; rw [ bound_add A μ h.p H.p,← pre_a, pours_a _ (granted M x _ (smooth_bind A μ h.p)) (granted M x _ (smooth_bind A μ H.p)),map_add,smul_add]
omit h
lemma commutes (h:Plausible E) : (PowerSeries.coeff k (orientation M x Y (fun j=> bound A μ E))).part p = (capital A μ)⁻¹ • ∫ z,T E p z ∂μ:= by
 rw [PowerSeries.coeff_mk,(price_mar M x Y μ A E (pension h) p).2, smul_smul, inv_mul_cancel₀ (capital_pos A μ|>.ne'),one_smul]; rfl
-- prefer directly book α
lemma granted_margin (P:Book (X×Z))(h:Plausible (P k)) : (PowerSeries.coeff k (orientation M x Y (fun j=> bound A μ (P j)))).part p=(capital A μ)⁻¹ • ∫ z,T (P k) p z ∂μ:= (show _=(PowerSeries.coeff k (orientation M x Y (fun j=> bound A μ (P k)))).part p from (by simp only [PowerSeries.coeff_mk])).trans (commutes M x Y μ A (P k) p h)
end YM.Qlocal.Quipu.Wall
