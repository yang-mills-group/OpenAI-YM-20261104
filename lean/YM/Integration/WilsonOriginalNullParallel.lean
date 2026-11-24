import YM.Integration.WilsonOriginalNullCanonicalStep
import YM.Integration.ActualOneMarkGraphStep

/-! A joint homogeneous Wilson step for the canonical and measured null
carriers. Each keeps its own physical hard owner list. The emitted field is the
single original calibrated column, including its unit coordinate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullParallel
open Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators
variable {G:Gauge} (C:Family G) (d N p i:ℕ) (W:∀ j,Rep G (C.side j p))
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d
local notation "Q₀" => store C d p
local notation "V₀" => value (C:=C) d N p
local notation "Y₀" => calValues (C:=C) d N p
local notation "κ" => LocalComparison.forcedDivisor C
local notation "L" => factor C i

/-- The two incoming densities are summed before the genuine conditional
integral. Its outputs use the same two carriers at the receiving date. -/
theorem original (H:C.Makes) (live:i<N) (home:Opened C d i p)
    {γ ε:ℝ} (canonical:Gate C d N p i γ ε)
    {y:Site (C.side (i+1) p)} (measured:WilsonOriginalNullCanonicalStep.Coupled C d N p i W y ε)
    {a b c δ η:ℝ} (law:(W (i+1)).Lawful a b c δ η)
    {h k:Q₀ (i+1)} {B D:ℝ}
    (hfit:h.Format y C.params (W (i+1))) (hpaid:h.remBound y (W (i+1)) (κ (i+1)) B)
    (hzero:projection F₀ C.params (W (i+1)).p.threshold y h=0)
    (kpaid:reads (C:=C) d N p (i+1) k D) (kzero:page (C:=C) d p (i+1) k=0) :
    ∃ (v w:Q₀ i) (x:C.label d) (u e:ℝ),
      v.Format 0 C.params (W i) ∧ v.remBound 0 (W i) (κ i) u ∧
      projection F₀ C.params (W i).p.threshold 0 v=0 ∧ reads (C:=C) d N p i w e ∧
      page (C:=C) d p i w=0 ∧ u+e ≤ L^(-rate)*(B+D) ∧
      L^rate*mCost C d N p i x ≤ ε*(B+D) ∧
      transition (C:=C) d N p i (h.density y S₀ (W (i+1)) + V₀ (i+1) k)=
        v.density 0 S₀ (W i)+V₀ i w+Y₀ i x := by
  obtain ⟨v,w,x,u,e,vf,vp,vn,wr,wn,bill,xf,hs⟩:=measured h B hfit hpaid hzero
  obtain ⟨z,j,zr,zn,jf,ks⟩:=canonical.2 k D kpaid kzero
  have credit:=presentation wr.1 wr.2 zr.1 zr.2
  refine ⟨v,beside w z,x+j,u,e+L^(-rate)*D,vf,vp,vn,credit,?_,?_,?_,?_⟩
  · rw [addPage d N p i w z H home.post live.le wr zr,wn,zn,add_zero]
  · rw [mul_add,←add_assoc];exact add_le_add bill (le_refl _)
  · have price : mCost C d N p i (x+j) ≤ mCost C d N p i x+mCost C d N p i j := by
      change (F₀).coeffSize (measuring C d N p i (x+j)) ≤ _
      rw [measuring_add C d N p H home live.le]
      exact Size.add ..
    calc
      L^rate*mCost C d N p i (x+j) ≤ L^rate*(mCost C d N p i x+mCost C d N p i j) :=
        mul_le_mul_of_nonneg_left price (Real.rpow_nonneg (zero_lt_one.trans (factor_positive C i)).le _)
      _ = _+_ := mul_add ..
      _ ≤ _ := (add_le_add xf jf).trans_eq (mul_add ε B D).symm
  · have hi:=(h.envelope S₀ law hpaid hfit).integrableC (prior G _)
    have ki:=message d N p (i+1) H (home.post.trans i.le_succ) live kpaid
    rw [transition_add (C:=C) d N p hi ki,hs,ks,show V₀ i (beside w z)=V₀ i w+V₀ i z from
      plus (H.wilson.represents N p i live.le).good wr.2 zr.2 S₀,
      cal_add d N p i H home.post live.le]
    abel

end YM.Integration.WilsonOriginalNullParallel
