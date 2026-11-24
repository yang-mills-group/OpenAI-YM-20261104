import YM.FVA2.XPos.Tangent
import YM.X.Gauss.Expect
/-!
# XSpace's actual Taylor polynomial convention and normalized blend moments, in the chosen gauge
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.XPos
open Function Set Filter Finset Lattice Wilson
open Orbit Orbit.Screen Orbit.Grove Laplace XSpace
open PertExtension PertExtension.Series PertExtension.Orb Radial GaussianScore
open MeasureTheory Measure PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice Next.Rank.Normal
open Wick.Boson (cost cost_at coord balance paper_atoms atoms)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {R:XSpace.Period}(T:R.Tree)
local notation "E"=> T.Field G
local notation "P"=> Bare.Vertices T G
local notation "χ"=> Taylor.evalAt ( XSpace.Period.Tree.basis T G )
local notation "B"=> XSpace.Period.Tree.basis T G
local notation "Q"=> XSpace.Bare.Q T G
local notation "K"=> Permit (T.Field G)
variable {I:Type*} -- no spaces
lemma stirred (i:T.Key G)(x:E) : χ x (MvPolynomial.X i)=(↑((Wick.Boson.coord B i).val x):ℂ):= MvPolynomial.aeval_X ..
lemma balloons (t:Type) (p:Finset t)(s:t→ T.Key G)(x:E): χ x (glyphs s p)=(↑((cost B s p).val x):ℂ):= by unfold glyphs; rw [cost_at, Law.product, map_prod, Complex.ofReal_prod ]; exact prod_congr rfl fun i _=> stirred T (s i) x
-- transport arbitrary real polynomials and hence Taylor jets
lemma realizes (y: Permit (T.Field G)) : ∃ f:P,∀ x:E, χ x f = (↑(y.val x):ℂ):= by
 let S (f:E→ℝ):= ∃ p:P,∀ x:E, χ x p=(↑(f x):ℂ)
 have h (u:E→ℝ)(hu:u∈ Submodule.span ℝ (↑(Submonoid.closure (atoms B)))): S u:= by
    induction hu using Submodule.span_induction with
    | mem u hu=> obtain ⟨n,p,rfl⟩:= Wick.Boson.monomial B u hu; exact ⟨_,balloons T (Fin n) _ p⟩
    | zero=> exact ⟨0,fun x=> by simp⟩
    | add f g _ _ h k=> obtain ⟨p,h⟩:=h; obtain ⟨q,hq⟩:=k; exact ⟨p+q,fun x=> by rw [map_add,h,hq,Pi.add_apply,Complex.ofReal_add]⟩
    | smul a f _ h => obtain ⟨p,h⟩:=h; exact ⟨ (a:ℂ) • p,fun x=>by rw [map_smul,h,Pi.smul_apply];simp only [smul_eq_mul,Complex.ofReal_mul]⟩
 exact h y.val (paper_atoms B y)
private def page (p:K) := ( realizes T p ).choose
private lemma pager (p:K)(x:E): χ x (page T p)= (↑(p.val x):ℂ):= (realizes T p).choose_spec x
-- no shadow page in other ns
variable (G) in
def install : Permit (T.Field G)→ₐ[ℝ] Bare.Vertices T G where
 toFun:=page T
 map_one':= Taylor.from_real ( B ) _ _ (fun x=> by rw [pager,map_one]; rfl)
 map_zero' := Taylor.from_real ( B ) _ _ (fun x=> by rw [pager,map_zero]; rfl)
 map_mul' p q := Taylor.from_real ( B ) _ _ (fun x=> by rw [pager,map_mul,pager,pager]; exact Complex.ofReal_mul ..)
 map_add' p q:= Taylor.from_real ( B ) _ _ (fun x=> by rw [pager,map_add,pager,pager]; exact Complex.ofReal_add ..)
 commutes' c:= Taylor.from_real ( B ) _ _ (fun x=> by rw [pager,show (algebraMap ℝ (Bare.Vertices T G)) c = MvPolynomial.C (c:ℂ) from rfl,Taylor.evalAt,MvPolynomial.aeval_C]; rfl)
local notation "π"=> install G T
lemma contact (f:K)(x:E): χ x (π f)= (↑(f.val x):ℂ):= pager ..
lemma source (t:Type) (p:Finset t)(s:t→ T.Key G) : π (cost B s p)= glyphs s p:= Taylor.from_real B _ _ (fun x=> by rw [balloons,contact])

variable (μ:Measure (T.Field G))[μ.IsAddHaarMeasure]
lemma slides : PositionX.Gauss.formed (Module.Basis.coord ( B )) (Qx G T)=Bare.Q T G:= by apply Symmetric.ext; funext i j; rw [read_Q, Wick.Boson.Monitor];rfl
lemma peers (p:K): blend Q 0 (π p)= ↑( Papers.opening μ (Qx G T) p ):= by
 let W:= Qx G T; let L:Permit (T.Field G)→ₗ[ℝ]ℂ:= (blend Q 0).restrictScalars ℝ ∘ₗ (π).toLinearMap - Complex.ofRealCLM.toLinearMap ∘ₗ Papers.opening μ W;
 let S (f:E→ℝ):= ∃ x:Permit (T.Field G), x.val=f ∧ L x=0
 have h (f:E→ℝ)(hi:f∈ Submodule.span ℝ (↑(Submonoid.closure (atoms B)))) : S f := by
    induction hi using Submodule.span_induction with
    | mem f h=> obtain ⟨l,f,rfl⟩ := Wick.Boson.monomial B f h; refine ⟨ cost B f Finset.univ,rfl,sub_eq_zero.mpr ?_⟩; change blend Q 0 (π (Wick.Boson.cost B f Finset.univ))= (↑( W.average _ _ ):ℂ); rw [source, ← slides T,← PositionX.Gauss.glyph (Qx G T) μ]; exact congr_arg (fun a=> (↑( W.average μ a):ℂ)) (funext (fun x=> (cost_at B f _ x).symm))
    | zero => exact ⟨0,rfl,map_zero L⟩
    | add => rename_i y v a l ia il; obtain ⟨y,rfl,ha⟩:=ia; obtain ⟨v,rfl,h⟩:=il; exact ⟨ y+v,rfl,by rw [map_add,ha,h,add_zero]⟩
    | smul => rename_i y u a l; obtain ⟨v,rfl,h⟩:=l; exact ⟨_,(show (y • v).val= y • v.val from rfl), by rw [map_smul,h,smul_zero]⟩
 obtain ⟨v,h,H⟩:=h p.val (paper_atoms B p); exact sub_eq_zero.mp ((Subtype.ext h:v=p) ▸ H : L p = 0)

local notation "τ"=> (PowerSeries.map ( AlgHom.toRingHom ( π ) ))
lemma parse (f:E→ℝ)(h:ContDiffAt ℝ ∞ f 0): τ (Stack.rise f)= Taylor.expandTaylor ( B ) (Complex.ofRealCLM ∘ f) := by
 apply PowerSeries.ext; intro n; rw [coeff_map,Taylor.expandTaylor, coeff_mk]; apply Taylor.from_real B; intro x; change χ x ( π _ )=_; rw [contact, ← Stack.reading_term, Stack.read_rise, Taylor.divided_realEval]; · rfl
 exact h.of_le (WithTop.coe_le_coe.mpr le_top)
lemma rates : τ (Stack.advancing (T.action (G:=G)))= Bare.interaction T G := by
 apply PowerSeries.ext; intro n; by_cases h:n=0; · subst n; rw [coeff_map, coeff_zero_eq_constantCoeff_apply,Stack.advancing_zero,map_zero]; rw [coeff_zero_eq_constantCoeff_apply,Bare.interaction_initial]
 rw [coeff_map]; apply Taylor.from_real B; intro x; change χ x (π _)= _; rw [contact, ← Stack.reading_term, Stack.levels,Bare.interaction_coeff T x h]; unfold Radial.layers; rw [if_neg h]; simp only [add_zero,Complex.ofReal_neg]; rfl
lemma heater : τ (Laplace.sink (XSpace.Bare.relative (G:=G) T) T.action)= Bare.weight T G:= by
 rw [Laplace.sink,map_mul,parse T _ ((Bare.relative_smooth T G).of_le le_top),Bare.weight,mul_comm]; refine congr_arg₂ (·*·) rfl ?_; apply PowerSeries.ext; intro n; rw [coeff_map, Stack.exponential, coeff_mk,_root_.map_sum,_root_.map_sum,Bare.exponential_formula]; apply sum_congr rfl; intro i hi; rw [ Stack.roll, coeff_C_mul, map_mul,← rates T,←map_pow,coeff_map ]; refine congr_arg₂ (·*·) ?_ rfl; rw [show (π).toRingHom _ = _ from (π).commutes _, show algebraMap ℝ ( Bare.Vertices T G ) _= _ from rfl]; simp [one_div]
local notation "ρ"=> PowerSeries.map Complex.ofRealHom
lemma parch (k:Ticket (T.Field G)): Bare.diagrams T G (τ k) = ρ (input (Qx G T) μ (Laplace.sink (XSpace.Bare.relative T) T.action * k)):= by
 apply PowerSeries.ext; intro n; rw [Bare.diagram_coeff,← heater T,←map_mul,coeff_map,coeff_map]; simp only [input,throughPrice,AddMonoidHom.coe_mk,ZeroHom.coe_mk,coeff_mk]; exact peers T μ (coeff n (Laplace.sink (XSpace.Bare.relative T) T.action * k))
lemma receipt_X (k:Ticket (T.Field G)): Bare.normalized T G (τ k) = ρ (enjoy (Qx G T) μ k (Laplace.sink (XSpace.Bare.relative T) T.action)):= by
 let Γ:= Qx G T; let z:=Laplace.sink (XSpace.Bare.relative (G:=G) T) T.action; have hz:constantCoeff (input Γ μ z)=1:=underBudget Γ μ (Laplace.stamp _ _ (Bare.relative_one T G)); have hp : Bare.vacuum T G=ρ (input Γ μ z):= Eq.trans ( show Bare.vacuum T G=Bare.diagrams T G ( τ (1:Ticket (T.Field G)) ) from congr_arg (Bare.diagrams T G) (map_one _).symm ) (by rw [parch T μ 1,mul_one]); symm; apply Bare.denominator_determines; change ρ (enjoy Γ μ _ z) * _=_; rw [hp,←map_mul, enjoy, mul_assoc, PowerSeries.inv_mul_cancel _ (by rw [hz]; exact one_ne_zero), mul_one]; exact (parch T μ k).symm

-- XSpace.Bare.normalized is the same independent Wilson calculation
variable {O:Config G R.side→ ℝ}
include μ
theorem raw_X (h:PertExtension.Orb.PreTest O): Bare.normalized T G ( Taylor.expandTaylor ( B ) (Complex.ofRealCLM ∘ (O ∘ T.links)))= ρ (PowerSeries.mk (Orb.diag (Orb.restrictedO O))):= by
 rw [ ← parse T _ (hears T h),prices T h μ, receipt_X T μ]
omit μ
theorem genuine_X (h:PertExtension.Orb.PreTest O): Bare.normalized T G ( Taylor.expandTaylor ( B ) (Complex.ofRealCLM ∘ (O ∘ T.links)))= ρ (PowerSeries.mk (Orb.diag (Orb.restrictedO O))):= raw_X T addHaar h
end YM.FVA2.XPos
