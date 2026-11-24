import YM.Integration.WilsonCapturedFactoryCocycle
import YM.Integration.WilsonCapturedSignedCrossing

/-! The true fixed-reference contraction, starting with ordinary,
unshifted physical source evolution on an original finite cutoff.
The exact calibrated cocycle preserves that signed forcing after
subtracting the unique matrix coordinate chosen by the lower germ. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedOriginalCrossing
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 YM.MergeProof Germ
open WilsonCapturedFactoryCocycle
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d : ℕ)

theorem purchased (hG : G.Simple) {γ ε : ℝ} (hγ : 0<γ) (hγ' : γ<rate)
    (he : 0<ε) (he' : ε≤1) :
    ∀ᶠ t : ℕ in atTop, ∀ p N, t≤N → ∀ (qt : store R.family d p t) {rt : ℝ},
      reads (C:=R.family) d N p t qt rt →
      ∃ x : R.family.label d, page (C:=R.family) d p t ((R.family.factory d N p).entries t x) =
          page (C:=R.family) d p t qt ∧
      ∀ {b : ℕ} (_ : t≤b) (_ : b≤N) (qb : store R.family d p b)
        {rb D : ℝ} (_ : reads (C:=R.family) d N p b qb rb)
        (_ : (R.family.labels.level d).coeffSize qb.x ≤ rb) (_ : 0≤D)
        {raw f : Er R.family p},
        raw t = value (C:=R.family) d N p t qt →
        raw b = value (C:=R.family) d N p b qb →
        (∀ i≥t, i<b → Foreground R.family d N p i (f i) D ∧
          raw i = transition (C:=R.family) d N p i (raw (i+1)) + f i) →
        let B := (1+4*stock R.family b)*rb
        ∃ (Q : ∀ i, store R.family d p i) (y : ℕ→R.family.label d), ∀ i≥t, i≤b →
          Shot R.family d N p (subtract R d N p x raw) i (Q i) (y i) (hike R.family b i rate*B+2*D) ∧
          mCost R.family d N p i (y i) ≤
            hike R.family t i γ*(2*((i:ℝ)-t)*D) + 2*ε*hike R.family b i rate*B := by
  obtain ⟨s,opened⟩ := Filter.eventually_atTop.mp (open_late R.family hG d)
  filter_upwards [WilsonCapturedSignedCrossing.purchased R d hG hγ hγ' he he',
    Filter.eventually_ge_atTop s] with t buy st
  intro p N tN qt rt paid
  obtain ⟨x,correction,signed⟩ := buy p N tN qt paid
  refine ⟨x,correction,?_⟩
  intro b tb bN qb rb D bought bare D0 raw f left right original
  obtain ⟨v,y,hv,zero,sliced,_,_⟩ := fresh_split (C:=R.family) (d:=d) (N:=N) (p:=p)
    (i:=b) R.makes (opened b (st.trans tb) p) bN qb bought bare
  have top : ∃ a z, Shot R.family d N p raw b a z ((1+4*stock R.family b)*rb) :=
    ⟨v,y,⟨hv,zero,right.trans sliced⟩⟩
  have keep := propagation R d N p (opened t st p).post bN x raw f original top
  have start : (subtract R d N p x raw) t = value (C:=R.family) d N p t qt -
      calValues (C:=R.family) d N p t x :=
    congrArg (fun z => z-calValues (C:=R.family) d N p t x) left
  have cap : (subtract R d N p x raw) b = value (C:=R.family) d N p b qb -
      calValues (C:=R.family) d N p b x :=
    congrArg (fun z => z-calValues (C:=R.family) d N p b x) right
  exact signed tb bN qb bought bare D0 start cap keep

end YM.Integration.WilsonCapturedOriginalCrossing
end
