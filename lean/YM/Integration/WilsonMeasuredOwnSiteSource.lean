import YM.Integration.WilsonMeasuredCourseSourceGerm
import YM.Integration.WilsonThermometerOwnOffsetField

/-! The actual compensated Wilson singleton on its named measured course,
at every upper cutoff and its actual projected site. The two spectator
numerators remain attached to their respective physical histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnSiteSource
open Filter Lattice Wilson RG RG.Shoot Marker Overlay Source Labels Extra.Histories Relay
open PhysicalNext Repeat Legato Graces Roost Pressure Testing Input Precision Org Supply Push
open SectorMeasure PriceCompiler ConnectedActivityE6 Progress.DirectedRecipe
open AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open RG05Readout Native Address Many RG05Readout.Records MergeProof Accent
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue Push.Local
open scoped Topology Classical
variable {G:Gauge}

private theorem bring {n:Side} {d:ℕ} {F:Frame G d}
    (A:Hol G) (o:Site n) (q:Coefficient F n) (X Y:Rep G n)
    (base:X.p=Y.p) (same:X.activities.forced=Y.activities.forced)
    (old:q.Format o A X) {κ m:ℝ} (paid:q.remBound o X κ m) :
    q.Format o A Y ∧ q.remBound o Y κ m := by
  refine ⟨⟨?_,old.origin,old.identity_null,old.projects,?_,?_,old.invariant,?_,old.borel⟩,?_⟩
  · simpa only [←base] using old.smooth
  · simpa only [←base,←same] using old.forcing
  · simpa only [←same] using old.carried
  · simpa only [←base,←same] using old.supported
  · simpa only [Coefficient.remBound,←base,←same] using paid

theorem original (R:Run G) {start base d m N per k:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j,Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ start N per k Ψ)
    (since:start ≤ m) {D:Rail R.family} {B:ℕ→ℕ→ℝ} {V:Sight R.family d per}
    {r:Emblems R.family d} (z:Site (R.family.side N per))
    (gauge:Enrolled R.makes D B base N per d (digits R N per z) V r)
    (aged:base ≤ m) (live:m ≤ N) (starts:∀ e ≤ d,R.family.ref e ≤ N) (y:Palette R.family d) :
    let C:=R.family
    let P:=C.path.rep N per m
    let W:=Ψ m
    let o:=(C.S.toDepth live per).parent z
    let t:=primaryLetter d
    let x:=(C.factory d N per).terminal (finer r live y t)
    let E:=dyes C m N per live ((C.S.a m:ℂ)^d • C.O N per x z)
    let g:=kappa C.path m
    let M:=B d m*size y
    ∃ X Q:Coefficient (C.labels.level d) (C.side m per),
      Trace.Physical.Germ.projection (C.labels.level d) C.params W.p.threshold 0 X=y t ∧
      X.Format 0 C.params W ∧ X.remBound 0 W g M ∧
      Q.Format o C.params W ∧ Q.remBound o W g M ∧ Q.density o (C.localSection d) P=E ∧
      (∀ U, Q.density o (C.localSection d) W U-E U =
        ActualWilsonGraphReclosure.gas W Q U-ActualWilsonGraphReclosure.gas P Q U) ∧
      Q.density o (C.localSection d) W =ᶠ[𝓝 1] E := by
  intro C P W o t x E g M
  obtain ⟨base,same,_⟩ := WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course since live
  change P.p=W.p at base
  change P.activities.forced=W.activities.forced at same
  obtain ⟨X,Q,head,fx,bx,fq,bq,_,truth⟩ :=
    WilsonThermometerOwnOffsetField.actual R N per m z gauge aged live starts y
  obtain ⟨f₀,b₀⟩ := bring C.params 0 X P W base same fx bx
  obtain ⟨f₁,b₁⟩ := bring C.params o Q P W base same fq bq
  change Q.density o (C.localSection d) P=E at truth
  have vacuum:W.eval=P.eval := (later R π Γ Ψ course since live).view
  have diff (U:Config G (C.side m per)) : Q.density o (C.localSection d) W U-E U =
      ActualWilsonGraphReclosure.gas W Q U-ActualWilsonGraphReclosure.gas P Q U := by
    rw [←truth]
    change ((W.eval U:ℂ)*Q.exponentialEntry o (C.localSection d) W U+ActualWilsonGraphReclosure.gas W Q U)-
      ((P.eval U:ℂ)*Q.exponentialEntry o (C.localSection d) P U+ActualWilsonGraphReclosure.gas P Q U)=_
    rw [vacuum]
    simp only [Coefficient.exponentialEntry,Coefficient.maskedTerm,base]
    abel
  refine ⟨X,Q,?_,f₀,b₀,f₁,b₁,truth,diff,?_⟩
  · rw [←base]
    exact head
  · filter_upwards [Juniper.Caret.flat_flags (C.side m per) P.p.threshold P.p.threshold_pos] with U hU
    have hw : flags W.p.threshold U=∅ := by simpa only [←base] using hU
    have yes := diff U
    rw [ActualWilsonGraphReclosure.gas_unflagged W Q U hw,
      ActualWilsonGraphReclosure.gas_unflagged P Q U hU,sub_self] at yes
    exact sub_eq_zero.mp yes

end YM.Integration.WilsonMeasuredOwnSiteSource
end

