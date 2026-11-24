import YM.FrontierTrace.Primary.Law

/-!
# Rank-four physical measuring fields cancel renormalization constants

DOES NOT imply comparison at a finite change of scale or amount of growth
on either pole. The identities hold on exact state & operator with `Paying`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace.Primary
open Function Set Filter Analysis Labels Maxwell Maxwell.Free Table
open UVNext.FreeStress Next.UVStress Work.A01 Trace
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order}(F:Spec.Final C f S)
    (P : Spin.change S 4) (h:G.Simple)
local notation "L"=> C.labels.level 4
local notation "D"=> freeTable C.labels
local notation "Θ4" => metric0 C.labels
local notation "Σ4" => scalarLabel C.labels

def footing (C: Family G) (k:C.label 4)(s:ℝ): C.label 4:= s • k
lemma local_ne : (C.S.a (C.ref 4))^4≠0:= pow_ne_zero _ (C.S.a_pos _).ne'

def realProjection : C.label 4 ≃ₗ[ℂ] S.Field 4:= LinearEquiv.ofBijective (S.project 4) (actual_projection P h le_rfl)
local notation "Rt"=> realProjection P h
local notation "Q₀"=> projectEquiv C h

lemma realV (x:C.label 4): Rt x= S.project 4 x:=rfl
/-- Pulls THE moving P back to literal labels. -/
def switchLeg : LegOrder C := (Q₀).trans (P.trans (Rt).symm)
local notation "H₀"=> switchLeg P h
lemma payed (x: C.label 4):P (Q₀ x) = Rt (H₀ x):= by
     simp only [switchLeg,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
lemma payedRule (hp : Paying F P): LegRule C H₀ := by
   have hc:= hp.cov
   constructor
   · intro x k; apply (Rt).injective; rw [← payed]
     rw [show (Q₀ ((L).act k.ortho x)) = (D).mirror (spin_free C.labels) 4 k ((Q₀) x) from ((D).mirror_project ..).symm,hc.1 k]
     rw [payed P h]; exact S.mirror_project ..
   · intro x; apply (Rt).injective; rw [← payed]
     have he:= show (Q₀) (star x)=(D).conj (spin_free C.labels) 4 ((Q₀) x) from ((D).conj_project ..).symm
     rw [he,hc.2,payed P h]; exact S.conj_project ..
   let b:ℝ:=(C.S.a (C.ref 4))^4; refine ⟨(b:ℂ),Complex.ofReal_ne_zero.mpr (local_ne (C:=C)),?_⟩
   apply (Rt).injective; rw [← payed,e0R]; unfold b; rw [Complex.ofReal_pow]; exact hp.paid_unit

include h in
lemma physicalP (hp : Paying F P) : ∃ p q w : ℝ,p≠0∧w≠0 ∧
   P Σ4 = p • S.project 4 (scalarKey C) + q • S.unit 4 ∧
   (∀ (i j:Axis),i≠j→P (Θ4 i j) = w • S.project 4 (metricKey C i j)):= by
   let f:= H₀
   obtain ⟨p,q,hp0,h₁⟩:= chart_scalar C h (payedRule F P h hp); obtain ⟨w,hw,h₂⟩:= chart_metric C h (payedRule F P h hp)
   let t:ℝ:= (C.S.a (C.ref 4))^4; have hK : t≠0:=local_ne (C:=C)
   have hz : S.unit 4= t • (Rt (L).e0):=by
      let z:ℂ:= ((C.S.a (C.ref 4):ℂ))^4; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), ← map_smul]; change Rt (z • (L).e0)= _; congr 2; exact (Complex.ofReal_pow ..).symm
   have ho (u:ℝ)(x:C.label 4) : Rt (u • x)=u • (Rt x):= ((Rt).toLinearMap.restrictScalars ℝ).map_smul ..
   refine ⟨p,q/t,w,hp0,hw,?_,?_⟩
   · rw [← show Q₀ _=_ from project_scalar C h, payed,h₁,map_add,ho,ho,hz,smul_smul,div_mul_cancel₀ q hK]; rfl
   intro i j hij; rw [← project_metric C h i j hij,payed,h₂ _ _ hij, ho]; rfl

/- top-source real reparametrization independent of P. -/
open Lattice Wilson Source
variable (N p:ℕ)
lemma places_add (o:Site (C.side N p))(x y:C.label 4)(U:Config G (C.side N p)):
    (C.localSection 4).places (x+y) o U=(C.localSection 4).places x o U+(C.localSection 4).places y o U:=
    congr_fun ((C.localSection 4).eval_linear.map_add x y) (expandAt o U)
lemma places_scalar (o:Site (C.side N p))(x:C.label 4)(v:ℂ)(U:Config G (C.side N p)):
    (C.localSection 4).places (v • x) o U=v • (C.localSection 4).places x o U:=
    congr_fun ((C.localSection 4).eval_linear.map_smul v x) (expandAt o U)
lemma topExpressions (hc:C.Makes) (a b u:ℝ) (h₁:(C.factory 4 N p).terminal.symm (scalarKey C)=a • scalarKey C+b • (L).e0)
    (h₂:∀ i j:Axis,i≠j→ (C.factory 4 N p).terminal.symm (metricKey C i j) = u • metricKey C i j)
    (o:Site (C.side N p)): let t:= C.path.levels.clock.threshold N; let k:ℝ:= (C.S.a N)^4;
     C.O N p (scalarKey C) o=(k⁻¹*(a*t⁻¹^2)) • ((C.localSection 4).places (scalarKey C) o) + (fun _=>((k⁻¹*b:ℝ):ℂ)) ∧
       ∀ i j:Axis,i≠j→C.O N p (metricKey C i j) o=(k⁻¹*(u*t⁻¹^2)) • ((C.localSection 4).places (metricKey C i j) o):=by
   intro t k
   constructor
   · unfold Family.O Source.TransferData.cylinder; rw [show (C.factory 4 N p).terminal.symm (scalarKey C)=_ from h₁]; funext U
     unfold Source.initial; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) a, RCLike.real_smul_eq_coe_smul (K:=ℂ) b]
     simp only [Pi.add_apply,Pi.smul_apply,map_add,map_smul]
     rw [ show (L).scaled _ (scalarKey C) = ((t⁻¹^2:ℝ):ℂ) • scalarKey C from ((L).scaled_pure t⁻¹ _ (scalarGrade G)), (L).scaled_unit,places_add,places_scalar,places_scalar,places_scalar]
     rw [show (C.localSection 4).places (L).e0 o U=1 from congr_fun (hc.sections 4).unit (expandAt o U)]
     unfold k; simp only [Complex.real_smul,smul_eq_mul]; push_cast; ring!
   intro i j hij; unfold Family.O Source.TransferData.cylinder; rw [show (C.factory 4 N p).terminal.symm _ = _ from h₂ i j hij]; unfold Source.initial; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) u,map_smul,show (L).scaled _ (metricKey C i j) = ((t⁻¹^2:ℝ):ℂ) • metricKey C i j from ((L).scaled_pure t⁻¹ _ (metricGrade G i j))]; funext U; rw [Pi.smul_apply,Pi.smul_apply,places_scalar,places_scalar]; unfold k; simp only [Complex.real_smul,smul_eq_mul]; push_cast; ring!

include h in
lemma topFields (hc:C.Makes)(hN:C.ref 4≤N):∃ s t u:ℝ,s≠0∧ u≠0 ∧
   ∀ o:Site (C.side N p), C.O N p (scalarKey C) o= s • ((C.localSection 4).places (scalarKey C) o) + (fun _=>(t:ℂ)) ∧
     ∀ i j:Axis,i≠j→ C.O N p (metricKey C i j) o= u • ((C.localSection 4).places (metricKey C i j) o):=by
   let H:=rule_symm C _ (actual_rule C hc (p:=p) hN)
   obtain ⟨a,b,ha,h₁⟩:= chart_scalar C h H
   obtain ⟨u,hu,h₂⟩:= chart_metric C h H
   let t:= C.path.levels.clock.threshold N
   let k:ℝ:=(C.S.a N)^4; have ht:t≠0:=(C.path.levels.budget N).threshold_pos.ne'; have hk:k≠0:= pow_ne_zero _ (C.S.a_pos _).ne'
   refine ⟨k⁻¹*(a*t⁻¹^2),k⁻¹*b,k⁻¹*(u*t⁻¹^2),mul_ne_zero (inv_ne_zero hk) (mul_ne_zero ha (pow_ne_zero _ (inv_ne_zero ht))), mul_ne_zero (inv_ne_zero hk) (mul_ne_zero hu (pow_ne_zero _ (inv_ne_zero ht))), fun o=> ?_⟩
   exact topExpressions N p hc a b u h₁ h₂ o
end YM.FrontierTrace.Primary
