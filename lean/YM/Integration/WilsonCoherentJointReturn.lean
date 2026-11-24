import YM.Integration.WilsonCoherentLampTicket

/-! Numerical charge for the physical compact-Haar roster against its
specific retained, independently calculable normalized finite Gaussian ticket. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentJointReturn
open PowerSeries Lattice Wilson RG Tree Precision
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Router RGComparison.Core16 FVA2 FVA2.CityHistory
open PhysicalNext.Repeat.Legato

variable {G : Gauge} {I : Type} [Fintype I] (J : I → Spool.Lamp G)
variable {c f : Side} (S : StepData c f) (T : Forest S.ratio) (Z : ChartRatio G)
variable (u : Pins G c) (o : I → Site f) (large : Bid.Larger (G:=G) S)
variable (b : S.Choices) (v : (Descent.nil (top:=f)).Tags)

def term (part : Bool) (k : ℕ) : ℝ := coeff (Spool.power J+k) (Stack.read u
  (solenoid S T Descent.nil v b Z 1 large (show (Descent.nil (top:=f)).Room G from trivial)
    (Stack.rise (WilsonCoherentLampTicket.source J S T o part))))

def series (k : ℕ) : ℂ :=
  ⟨term J S T Z u o large b v false k,term J S T Z u o large b v true k⟩

theorem same {P : Parcel.Oven S.patch} (X : P.Form G) (ratio : LocalRatio Z)
    (paid : P.Offers X S.kernel) (inside : ∀a,‖u a‖≤X.Q) :
    Spool.rank J S T X Z u o = series J S T Z u o large b v := by
  funext k
  have row (part : Bool) : Spool.rankℝ J S T X Z u o part k = term J S T Z u o large b v part k := by
    have h := congrArg (coeff (R:=ℝ) k)
      (WilsonCoherentLampTicket.booked J S T o part X Z ratio large u paid inside b v)
    simpa only [Stack.drop,coeff_mk,term] using h
  exact Complex.ext (row false) (row true)

variable (R : Run G) (i : ℕ)
local notation "H₀" => WilsonCoherentFiniteIssue.stagePatch R i
local notation "K₀" => R.family.path.levels.clock.kernel

/-- The same honest cutoff and constant pay the two signed components after
their full re-expression through the original charge. Both forests and the
genuine kernel choices are universal after the numerical transaction. -/
theorem purchased (branches : (H₀).Branches K₀ G) (q : ℝ) (hq : 0<q) :
    ∃ (P : Parcel.Oven H₀) (X : P.Form G), X.Q=q ∧ P.Offers X K₀ ∧
    ∀ {I : Type} [Fintype I] (J : I → Spool.Lamp G) (B : Lumen.Stage) (r : ℕ),
      ∃ (U : Lumen.Stage) (C : ℝ), U.Above B ∧ 0≤C ∧
      ∀ (per : ℕ),
        let S:=R.family.path.levels.clock.op i per
        ∀ (large : Bid.Larger (G:=G) S) (T : Forest S.ratio) (u : Pins G (R.family.side i per))
          (o : I → Site (R.family.side (i+1) per)) (b : S.Choices)
          (v : (Descent.nil (top:=R.family.side (i+1) per)).Tags), ‖u‖≤q →
          Spool.Price U r C (series J S T R.metals.O u o large b v) (Spool.reads J S u o) := by
  obtain ⟨P,X,width,paid,issue⟩ := WilsonCoherentFiniteIssue.purchased R i branches q hq
  refine ⟨P,X,width,paid,?_⟩
  intro I _ J B r
  obtain ⟨U,C,above,nonneg,all⟩ := issue J B r
  refine ⟨U,C,above,nonneg,?_⟩
  intro per S large T u o b v bound
  have inside (a : Edge (Site (R.family.side i per))) : ‖u a‖≤X.Q := by
    rw [width]
    exact (norm_le_pi_norm u a).trans bound
  rw [←same J S T R.metals.O u o large b v X R.alloy.B.ratio paid inside]
  exact (all per large T u bound).1 o

end YM.Integration.WilsonCoherentJointReturn
end
