import YM.RG06.Bare.Path
import YM.RG06.Bare.Powers
import YM.Bid.Source
/-!
# All bare fluctuation coefficients of the actual (not Pert variant) stencils

Full SectionData evaluation, no transparency/injectivity assumptions on the
polynomial on group matrices (may be redundant). Exposes the stop and both
endpoints of every read to downstream consumers. Support test is exact in the
cover including path visits; `Bid.pop` is used only to get the improved t-order
appropriate to the `g_N^-1 per slot` diagram prescription---we prove for the
common UV family separately that it holds. Purely operator-level identities.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.RG06.Rules
open Function Filter CubicMatch Lattice Wilson Labels Source RG
open scoped Matrix.Norms.Frobenius ContDiff Topology BigOperators Classical

variable {G : Gauge} {n : Side}{d m k : ℕ}{T : Finset Cover}
variable {F : Labels.Frame G d}
abbrev index := Source.Index G T

def matrixEntry (i j : Fin G.repDim) : G.Mat →ₗ[ℝ] ℂ :=
    { toFun M := M i j
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

def entryMap {T:Finset Cover} (H: Source.Index G T) : G.Mat →L[ℝ] ℂ :=
  let M := (matrixEntry H.2.1 H.2.2.1).toContinuousLinearMap
  if H.2.2.2 then (starL ℝ).toContinuousLinearMap.comp M else M

theorem entry_apply (z:index (G := G) (T := T))(U:CoverConfig G) : entry U z = entryMap z (G.mat (U z.1.val)) := by
  unfold entryMap Source.entry; split <;> rfl

def entryCoeff (v : Links ℤ G.Color)(z:index (G := G) (T := T))(e:ℕ) := entryMap z (exponential (v z.1.val) e)

def formulaRule (v:Links ℤ G.Color)(P:Formula G T) := MvPolynomial.eval₂Hom PowerSeries.C
    (fun z=>PowerSeries.mk (entryCoeff v z)) P

theorem formula_exact (v:Links ℤ G.Color)(P:Formula G T) : HasSeries
    (fun t=> MvPolynomial.aeval (Source.entry (expRay v t)) P)
    (formulaRule v P) := by
  simp_rw [MvPolynomial.aeval_eq_eval]; apply HasSeries.subst; intro z
  apply HasSeries.mk; simp_rw [entry_apply]; apply HasCoefficients.linear (E:=G.Mat) (entryMap z) (exponential_exact _)

def sectionRule (S : SectionData F)(v:Links ℤ G.Color)(c:F.Coeff):PowerSeries ℂ := formulaRule v (S.evalC c)

theorem section_exact (S : SectionData F)(v:Links ℤ G.Color)(c:F.Coeff) : HasSeries
    (fun t=> S.evaluate c (expRay v t)) (sectionRule S v c) := formula_exact ..

-- Padded cover lift, all sites & torus sizes
def liftAt (A : Directions G n) (o : Site n) : Links ℤ G.Color := fun q=> A (wrap n q.1+o,q.2)

theorem place_exact (S : SectionData F)(v:Directions G n)(o:Site n)(c:F.Coeff) : HasSeries
    (fun t=> S.places c o (expRay (X:=Per n) v t)) (sectionRule S (liftAt v o) c) := section_exact ..

-- Explicit plate series on an RG.Slot, and low-degree-power division for Pose/poly stencils
def slotPath (x:RG.Slot)(v:Links ℤ G.Color) : ℕ→ G.Color:=plate v 0 x.walk x.plaq.val.1 x.plaq.val.2

def slotSeries (x : RG.Slot)(v:Links ℤ G.Color)(i:G.ColorIndex):PowerSeries ℂ :=
  PowerSeries.mk fun e=> (↑(slotPath x v (e+1) i):ℂ)

lemma slot_coefficients (x:RG.Slot)(v:Links ℤ G.Color) : HasCoefficients (fun t=> x.eval (expRay v t)) (slotPath x v) := plate_exact v 0 x.walk _ _

theorem slot_series (x:RG.Slot)(v:Links ℤ G.Color)(i:G.ColorIndex) : HasSeries
    (fun t=> (↑(x.eval (expRay v t) i):ℂ)) (slotSeries x v i * PowerSeries.X) := by
  let L : G.Color →L[ℝ] ℂ:=Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have h : HasCoefficients (fun t:ℝ=> L (x.eval (expRay v t))) (fun e=> L (slotPath x v e)) := HasCoefficients.linear L (slot_coefficients x v)
  have he:slotSeries x v i * PowerSeries.X=PowerSeries.mk (fun e=> L (slotPath x v e)):=by
    ext1 u; cases u with
    | zero => rw [PowerSeries.coeff_mk]; simp [slotPath]
    | succ d=>rw [PowerSeries.coeff_succ_mul_X,slotSeries,PowerSeries.coeff_mk, PowerSeries.coeff_mk]; rfl
  rw [he]; exact HasSeries.mk _ h

open Bid in
def poseRule (B : Fin m→RG.Slot)(P:Pose G m)(l:ℕ)(v:Links ℤ G.Color) := residualPol P PowerSeries.C (fun z=>slotSeries (B z.1) v z.2) PowerSeries.X l

open Bid in
theorem pose_exact (B : Fin m→RG.Slot)(P: Pose G m)(l:ℕ)(hp: lows P l)(v:Links ℤ G.Color):
    HasSeries (fun t=> lumin P (mapped B (expRay v t))) (poseRule B P l v * PowerSeries.X^l) := by
  unfold lumin poseRule; simp_rw [MvPolynomial.aeval_eq_eval]; apply divide_rules _ _ hp (fun z=>slot_series (B z.1) v z.2)

open Bid in
/-- Expose the leading value (exact degree l only) normalized and the first useful power loss rule:
there *are no* inverse coupling powers for these stencils on these fluctuation rays. -/
theorem pose_leading (B:Fin m→RG.Slot)(P:Pose G m)(l:ℕ)(hp:lows P l)(v:Links ℤ G.Color) :
   CubicMatch.term l (fun t=>lumin P (mapped B (expRay v t))) =
   ∑ w∈P.support with count w=l, P.coeff w * w.prod (fun z i => (↑(linPath v (B z.1).offset
    (square (B z.1).plaq.val.1 (B z.1).plaq.val.2) z.2):ℂ)^i) := by
    have h:=divide_upper (pose_exact B P l hp v) 0
    rw [Nat.zero_add,PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    rw [h,poseRule,residual_lead P l hp]; refine Finset.sum_congr rfl fun w hw=>?_
    simp_rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply,slotSeries,PowerSeries.coeff_mk,slotPath,Nat.zero_add,plate_one]; rfl

-- Version with exact support check via S.stencil & Bid.pop
open Bid

theorem pop_basis (S : SectionData F)(h:pop S)(i:F.Index) :
    ∃ (b:ℕ)(B:Fin b→RG.Slot), (∀ j,(B j).stencil ⊆ S.stencil) ∧ ∃ (P:Pose G b), lows P (F.grades i).2 ∧
     S.evaluate (Pi.single i 1) = lumin P ∘ mapped B ∧
     ∀ v:Links ℤ G.Color, sectionRule S v (Pi.single i 1)=poseRule B P (F.grades i).2 v * PowerSeries.X ^ (F.grades i).2 := by
  obtain ⟨b,B,hb,P,hP,hl⟩ := h i
  refine ⟨b,B,hb,P,hl,hP,fun v=>?_⟩
  ext1 e
  have hh:= HasCoefficients.unique (section_exact S v (Pi.single i 1)) (pose_exact B P _ hl v) (Eventually.of_forall (fun t=> congr_fun hP (expRay v t)))
  exact congr_fun hh e

-- implementation independent of choice of the Pose presentation
def scaledRule (S : SectionData F)(v: Links ℤ G.Color)(i:F.Index) := PowerSeries.mk (fun k=> PowerSeries.coeff (k+(F.grades i).2) (sectionRule S v (Pi.single i 1)))

theorem scaled_exact (S : SectionData F) (h:pop S)(i:F.Index)(v:Links ℤ G.Color) :
    sectionRule S v (Pi.single i 1) = scaledRule S v i * PowerSeries.X ^ (F.grades i).2 := by
  obtain ⟨_,_,_,_,_,_,hr⟩ := pop_basis S h i
  unfold scaledRule; simp_rw [hr v,PowerSeries.coeff_mul_X_pow]; congr 1; ext1 k; simp

/-- EXPLICIT horizon dependence of pop: powers & stencil costs are per S. No estimate here
that its coefficients at a larger horizon agree: use `valid.projects` for the matched
jets or transmit/reannounce in RG_08. -/
theorem basis_rule (S : SectionData F)(h:pop S)(v:Directions G n)(o:Site n)(i:F.Index) :
    HasSeries (fun t=>S.places (Pi.single i 1) o (expRay (X:=Per n) v t))
      (scaledRule S (liftAt v o) i * PowerSeries.X ^ (F.grades i).2) := by
  rw [← scaled_exact S h]; exact place_exact ..
end YM.RG06.Rules
