import YM.Integration.WilsonOriginalNullPlacedStep
import YM.Integration.WilsonOriginalNullPlacedGate

/-! At an arbitrary real child the two carriers keep their genuine hard
rosters. Reclose their two canonical returns on P after extracting the
two measured coordinates on their common frame. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedParallel
open Function Filter Lattice RG Wilson MeasureTheory Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical BigOperators Topology
variable {G:Gauge} (C:Family G) (d N p i:ℕ)
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d

def Joined (W:∀ j,Rep G (C.side j p)) (y:Site (C.side (i+1) p)) (ε:ℝ) : Prop :=
  let upper:=C.path.rep N p (i+1)
  let lower:=C.path.rep N p i
  let o:=(C.path.levels.clock.op i p).ratio.parent y
  ∀ (h k:Coefficient F₀ (C.side (i+1) p)) (B D:ℝ),
    h.Format y C.params (W (i+1)) → h.remBound y (W (i+1)) (safety C (i+1)) B →
    projection F₀ C.params (W (i+1)).p.threshold y h=0 →
    k.Format y C.params upper → k.remBound y upper (safety C (i+1)) D →
    projection F₀ C.params upper.p.threshold y k=0 →
    ∃ (v w:Coefficient F₀ (C.side i p)) (x:C.label d) (u e:ℝ),
      v.Format o C.params (W i) ∧ v.remBound o (W i) (safety C i) u ∧
      projection F₀ C.params (W i).p.threshold o v=0 ∧ w.Format o C.params lower ∧
      w.remBound o lower (safety C i) e ∧ projection F₀ C.params lower.p.threshold o w=0 ∧
      u+e ≤ (factor C i)^(-rate)*(B+D) ∧ (factor C i)^rate*mCost C d N p i x ≤ ε*(B+D) ∧
      transition (C:=C) d N p i (h.density y S₀ (W (i+1))+k.density y S₀ upper) =
        v.density o S₀ (W i)+w.density o S₀ lower+(calValues (C:=C) d N p i x ∘ Lattice.translate o)

variable (R:Run G)
local notation "R₀" => R.family
theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) {ε:ℝ} (pos:0<ε) :
    ∀ᶠ i:ℕ in atTop, ∀ N p, i<N → ∀ W:∀ j,Rep G ((R₀).side j p), ∀ y:Site ((R₀).side (i+1) p),
      (∃ a b c d e:ℝ,(W (i+1)).Lawful a b c d e) →
      WilsonOriginalNullPlacedStep.Coupled R₀ d N p i W y ε → Joined R₀ d N p i W y ε := by
  have small:0 < min ε 1:=lt_min pos zero_lt_one
  have opening:=open_late R₀ simple d
  filter_upwards [opening,(tendsto_add_atTop_nat 1).eventually opening,WilsonOriginalNullPlacedGate.original R d simple shop small] with i home high canon
  intro N p live W y lawful opened
  obtain ⟨a,b,c,t,j,law⟩:=lawful
  let o:=((R₀).path.levels.clock.op i p).ratio.parent y
  intro h k B D hf hp hn kf kp kn
  obtain ⟨v,w,x,u,e,vf,vp,vn,wf,wp,wn,fee,saved,phy⟩:=opened h B hf hp hn
  obtain ⟨z,a,s,s0,zf,zp,zn,stockBill,hist⟩:=canon N p live (high p) (home p) y k D kf kp kn
  have dims:=dimensions d N p i R.makes (home p).post live.le
  have B0:0 ≤ B:=by obtain ⟨β,η,hβ,hη,full,-⟩:=hp;linarith only [hβ,hη,full]
  have D0:0 ≤ D:=by obtain ⟨β,η,hβ,hη,full,-⟩:=kp;linarith only [hβ,hη,full]
  let L:=factor R₀ i
  have lp:0<L:=zero_lt_one.trans (factor_positive R₀ i)
  have price0:0 ≤ mCost R₀ d N p i a:= Work.G08.size_nonneg _ _
  have stable:s ≤ L^(-rate)*D:=calc
    _ ≤ s + mCost R₀ d N p i a := le_add_of_nonneg_right price0
    _ ≤ min ε 1 * L^(-rate)*D := stockBill
    _ ≤ 1*L^(-rate)*D := by gcongr;exact min_le_right _ _
    _ = _ := by rw [one_mul]
  have primary:L^rate*mCost R₀ d N p i a ≤ ε*D:=calc
    _ ≤ L^rate*(min ε 1*L^(-rate)*D) := mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left s0).trans stockBill) (Real.rpow_nonneg lp.le _)
    _ = (L^rate*L^(-rate))*(min ε 1*D) := by ring
    _ = min ε 1*D := by rw [←Real.rpow_add lp,add_neg_cancel,Real.rpow_zero,one_mul]
    _ ≤ ε*D := mul_le_mul_of_nonneg_right (min_le_left _ _) D0
  have full:=presentation wf wp zf zp
  refine ⟨v,beside w z,x+a,u,e+s,vf,vp,vn,full.1,full.2,?_,?_,?_,?_⟩
  · rw [add_projection d w z wf zf dims.1 dims.2 ⟨_,_,wp⟩ ⟨_,_,zp⟩,wn,zn,zero_add]
  · rw [←add_assoc,mul_add];exact add_le_add fee stable
  · have plus:mCost R₀ d N p i (x+a) ≤ mCost R₀ d N p i x+mCost R₀ d N p i a:=by
      change ((R₀).labels.level d).coeffSize (measuring R₀ d N p i (x+a)) ≤ _
      rw [measuring_add R₀ d N p R.makes (home p) live.le];exact Size.add _ _ _
    calc
      _ ≤ L^rate*(mCost R₀ d N p i x+mCost R₀ d N p i a) := mul_le_mul_of_nonneg_left plus (Real.rpow_nonneg lp.le _)
      _ = _+_ := mul_add ..
      _ ≤ _ := (add_le_add saved primary).trans_eq (mul_add ε B D).symm
  · have pLaw:=(R.makes.wilson.represents N p (i+1) live).good
    have hi:=(h.envelope ((R₀).localSection d) law hp hf).integrableC (prior G _)
    have ki:=(k.envelope ((R₀).localSection d) pLaw kp kf).integrableC (prior G _)
    have both:=(plus (R.makes.wilson.represents N p i live.le).good wp zp ((R₀).localSection d))
    have united:((calValues (C:=R₀) d N p i (x+a)) ∘ Lattice.translate o)=
        ((calValues (C:=R₀) d N p i x) ∘ Lattice.translate o)+((calValues (C:=R₀) d N p i a) ∘ Lattice.translate o):=by
      exact congrArg (fun f:Config G ((R₀).side i p)→ℂ => f ∘ Lattice.translate o)
        (cal_add (C:=R₀) d N p i R.makes (home p).post live.le x a)
    let S:=(R₀).localSection d
    let lower:=(R₀).path.rep N p i
    let upper:=(R₀).path.rep N p (i+1)
    have grouped:(beside w z).density o S lower=w.density o S lower+z.density o S lower:=both
    calc
      _ = transition (C:=R₀) d N p i (h.density y S (W (i+1))) +
          transition (C:=R₀) d N p i (k.density y S upper) := transition_add (C:=R₀) d N p hi ki
      _ = (v.density o S (W i)+w.density o S lower+(calValues (C:=R₀) d N p i x ∘ Lattice.translate o))+
            (z.density o S lower+(calValues (C:=R₀) d N p i a ∘ Lattice.translate o)) :=
        congrArg₂ (·+·) phy hist
      _ = _ := by
        change _=v.density o S (W i)+(beside w z).density o S lower+(calValues (C:=R₀) d N p i (x+a) ∘ Lattice.translate o)
        rw [grouped,united];abel

end YM.Integration.WilsonOriginalNullPlacedParallel
