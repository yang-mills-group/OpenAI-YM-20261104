import YM.Integration.WilsonMatrixOriginalGermBasis
import YM.Integration.WilsonInheritedRegisteredField

/-! Exact normalized older Wilson fields from the original periodic intrinsic-germ coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermAnchor
open Lattice Wilson RG Source Labels Precision PhysicalNext.Repeat.Legato MergeProof
open Trace.Physical Trace.Physical.GermGraph FVA2 MS.Local.Physical MS.Menus
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonInheritedRegisteredField Finset
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (B:Deck G) {m N p:ℕ}

private def evaluation {X:Type*} (a:ℂ) (u:X) : (X→ℂ)→ₗ[ℂ]ℂ where
  toFun f:=a*f u
  map_add' f g:=mul_add a (f u) (g u)
  map_smul' c f:=mul_left_comm a c (f u)

private def reading (age:R.family.ref 4 ≤ m) (live:m ≤ N)
    (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)) : R.family.label 4→ₗ[ℂ]ℂ:=
  (evaluation (alto R.family.path m 4/((R.family.path.rep N p m).eval U:ℂ)) (pull 1 o U)).comp
    (WilsonMatrixOriginalGermBasis.density R.family R.makes 4 N p m age live)

private theorem anchor (age:R.family.ref 4 ≤ m) (live:m ≤ N) (w:R.family.label 4)
    (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    field R.makes live w o U=reading R age live o U ((R.family.factory 4 N p).terminal.symm w):=by
  let v:=(R.family.factory 4 N p).terminal.symm w
  have shift:=congrFun (WilsonTranslatedFactory.density R.makes live o v) U
  change alto R.family.path m 4*((WilsonTranslatedFactory.entry R.makes live o v).density o _ _ U)/
    ((R.family.path.rep N p m).eval U:ℂ) =
    (alto R.family.path m 4/((R.family.path.rep N p m).eval U:ℂ))*calValues (C:=R.family) 4 N p m v (pull 1 o U)
  rw [shift]
  simp only [Function.comp_apply]
  change _*calValues (C:=R.family) 4 N p m v (pull 1 o U)/_=_
  ring

private theorem lift {E W A:Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup W] [Module ℂ W] [Fintype A]
    (M:E→ₗ[ℂ] W) (fit:E≃ₗ[ℂ] E) (v:E) (a:A→ℂ) (s:A→E) (head:fit v=∑i,a i • s i):
    M v=∑i,a i • M (fit.symm (s i)):=by
  calc
    _=(M.comp fit.symm.toLinearMap) (fit v):=by simp
    _=_:=by rw [head,map_sum];simp only [map_smul,LinearMap.comp_apply,LinearEquiv.coe_coe]

private theorem submit {E A:Type*} [AddCommGroup E] [Module ℂ E] [Fintype A]
    (T fit:E≃ₗ[ℂ] E) (M:E→ₗ[ℂ] ℂ) (f:E→ℂ) (w:E) (a:A→ℂ) (s:A→E)
    (h:∀z,f z=M (T.symm z)) (head:fit (T.symm w)=∑i,a i • s i):
    f w=∑i,a i*f (T (fit.symm (s i))):=by
  have each (i:A):M (fit.symm (s i))=f (T (fit.symm (s i))):=by rw [h,T.symm_apply_apply]
  exact (h w).trans ((lift M fit _ a s head).trans (sum_congr rfl (fun i _=>congrArg (a i*·) (each i))))

def thermostat {d:ℕ} (F:Labels.Frame G d) (t:ℝ) (warm:t≠0):F.Coeff≃ₗ[ℂ] F.Coeff where
  toLinearMap:=F.scaled t
  invFun:=F.scaled t⁻¹
  left_inv x:=by
    change F.scaled t⁻¹ (F.scaled t x)=x
    simpa only [inv_inv] using F.scaled_inv (inv_ne_zero warm) x
  right_inv x:=F.scaled_inv warm x

/-- The observed engineering normalization precedes the original temperature map. -/
def clocked (m:ℕ) (t:ℝ) (warm:t≠0):R.family.label 4≃ₗ[ℂ] R.family.label 4:=
  (LinearEquiv.smulOfNeZero ℂ (R.family.label 4) ((R.family.S.a m^4:ℝ):ℂ)⁻¹
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (pow_ne_zero 4 (R.family.S.a_pos m).ne')))).trans
      (thermostat (R.family.labels.level 4) t warm)

def price (fit:R.family.label 4≃ₗ[ℂ] R.family.label 4) (w:R.family.label 4):Glyph B 4→ℂ:=
  weights (warehouse R) B 4 (fit ((R.family.factory 4 N p).terminal.symm w))

def issued (fit:R.family.label 4≃ₗ[ℂ] R.family.label 4) (i:Glyph B 4):R.family.label 4:=
  (R.family.factory 4 N p).terminal (fit.symm (column (warehouse R) B 4 i))

private theorem every (simple:G.Simple) (opened:Opened R.family 4 m p) (live:m ≤ N)
    (fit:R.family.label 4≃ₗ[ℂ] R.family.label 4) (w:R.family.label 4)
    (o:Site (R.family.side m p)) (U:Config G (R.family.side m p)):
    field R.makes live w o U=∑i,price R B (N:=N) (p:=p) fit w i*
      field R.makes live (issued R B (N:=N) (p:=p) fit i) o U:=by
  let T:=(R.family.factory 4 N p).terminal
  let a:=price R B (N:=N) (p:=p) fit w
  let x:=fit (T.symm w)
  have head:x=∑i,a i • (column (warehouse R) B 4 i:R.family.label 4):=resolution (warehouse R) B simple x
  exact submit T fit (reading R opened.post live o U) (fun z=>field R.makes live z o U) w a
    (fun i:Glyph B 4=>column (warehouse R) B 4 i) (fun z=>anchor R opened.post live z o U) head

/-- A single thermally scaled coordinate table at this observation year recovers the complete
normalized physical field on the original earlier Wilson law at every site and gauge input. -/
theorem field_at (simple:G.Simple) (opened:Opened R.family 4 m p) (live:m ≤ N)
    (t:ℝ) (warm:t≠0) (w:R.family.label 4):
    let fit:=(fitting 4 N p m R.makes opened live).trans (clocked R m t warm)
    let q:=(R.family.factory 4 N p).entries m ((R.family.factory 4 N p).terminal.symm w)
    let x:=clocked R m t warm (page (C:=R.family) 4 p m q)
    let a:=price R B (N:=N) (p:=p) fit w
    a=weights (warehouse R) B 4 x ∧
      (∑i,‖a i‖) ≤ (R.family.labels.level 4).coeffSize x*fare (warehouse R) B 4 ∧
      ∀o(U:Config G (R.family.side m p)),field R.makes live w o U=
        ∑i,a i*field R.makes live (issued R B (N:=N) (p:=p) fit i) o U:=by
  intro fit q x a
  have h:fit ((R.family.factory 4 N p).terminal.symm w)=x:=
    congrArg (fun y:R.family.label 4=>clocked R m t warm y)
      (fitting_apply 4 N p m R.makes opened live _)
  have same:a=weights (warehouse R) B 4 x:=congrArg (weights (warehouse R) B 4) h
  have limit: (∑i,‖a i‖) ≤ (R.family.labels.level 4).coeffSize x*fare (warehouse R) B 4:=by
    rw [same];exact bounded (warehouse R) B 4 x
  exact ⟨same,limit,every R B simple opened live fit w⟩

end YM.Integration.WilsonMatrixOriginalGermAnchor
