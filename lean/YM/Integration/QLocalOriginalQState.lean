import YM.Integration.QLocalHigherOrderBirth
import YM.Integration.QLocalReceivedWilsonState

/-! An authentic starting state for every later received signed history,
at both the requested and the raised finite marking order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalOriginalQState

open Function Filter Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open RG3.Script.Picnic QLocalReceivedWilsonState QLocalHigherOrderBirth MergeProof.Accent
open scoped Topology Classical

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B) (J:Request V) (A:NumericSchedule R.family J)
    (orders:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)

def Original (m:ℕ) : Prop := ∀ (d:LocalFormal.Datum R.family (Stock.census V)),d.level=m →
  ∀ (Q:MS.Land.Prescription B) (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (ks:V→ℕ)
    (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val),
  d.cutoff=d.level+1 →
  ∃ first:ActualOriginalQInitialInput.start R hG u J A orders≤d.level,
  ∃ I:FullPreparedInputAt (ActualOriginalQInitialInput.input R hG u J A d Q o μ ks orders first hp) 0,
    Retained.NativeIntake I ∧ I.carrier.rep=R.family.path.rep d.cutoff d.period (d.level+1) ∧
    I.regularPrice=0 ∧ I.forcedPrice=0 ∧
    State I (d.level+1) (fun t=>((ActualOriginalQInitialPreparation.input R hG u J A d Q o μ ks).leaf t).density)

omit [Nonempty V] in
private theorem read {n:Side} {W W':Rep G n} {o o':V→Site n} {X:Type} {Γ:Census V}
    {T:Taste X o W Γ} {T':Taste X o' W' Γ} (carrier:W=W') (roots:o=o') (marked:HEq T T') (x:X) :
    (T.leaf x).density=(T'.leaf x).density := by
  subst W' o'
  exact congrArg (fun S:Taste X o W Γ=>(S.leaf x).density) (eq_of_heq marked)

theorem of_birth {m:ℕ} (H:QLocalHigherOrderBirth.Born R hG u J A orders m) :
    Original R hG u J A orders m := by
  intro d hd Q o μ ks hp top
  obtain ⟨first,I,intake,carrier,full,regular,forced⟩:=H d hd Q o μ ks hp top
  refine ⟨first,I,intake,carrier,regular,forced,le_rfl,fun _=>le_rfl,fun t=>?_⟩
  rw [gust_base]
  exact read carrier rfl full t

theorem both (T:Campaign R) :
    ∀ᶠ m:ℕ in atTop,Original R hG u J A orders m ∧
      Original R hG u (raised J) (QLocalHigherOrderBirth.schedule A) orders m := by
  filter_upwards [QLocalHigherOrderBirth.both R hG u J A T orders] with m h
  exact ⟨of_birth R hG u J A orders h.1,of_birth R hG u _ _ orders h.2.1⟩

end YM.Integration.QLocalOriginalQState
