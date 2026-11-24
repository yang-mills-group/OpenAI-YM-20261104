import YM.Integration.WilsonCapturedOriginalCrossing
import YM.Integration.WilsonCapturedReturnedLabel

/-! Fixed reference counterterm for the true original unshifted
captured source. The identical bare x is now proved simultaneously to
be the unique lower periodic match, to have the complete true
subexponential return price, and to remove the stable germ in the
entire original forced contraction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedReturnedCrossing
open Filter Real Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph Work.G08 YM.MergeProof Germ
open WilsonCapturedFactoryCocycle
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d : ℕ)

/-- The price is simultaneously valid on every original capture up to
the actual cutoff N and for every permitted inverse loss η, after fixing
the physical reference, period, lower measured coordinate c and bare
label x once. -/
def Charged (N p t : ℕ) (M : ℝ → ℝ) (c x : R.family.label d) : Prop :=
  ∀ b ≥ t, ∀ hN : b ≤ N, ∃ ob : Opened R.family d b p, ∀ η > 0,
    let B := M η*(exp (η*(R.family.S.scale b-R.family.S.scale t))*
      (R.family.labels.level d).coeffSize c)
    (R.family.labels.level d).coeffSize ((fitting d N p b R.makes ob hN) x) ≤ B ∧
    reads (C:=R.family) d N p b ((R.family.factory d N p).entries b x) (2*stock R.family b*B)

theorem purchased (hG : G.Simple) {γ ε : ℝ} (hγ : 0<γ) (hγ' : γ<rate)
    (he : 0<ε) (he' : ε≤1) :
    ∃ M : ℝ → ℝ, (∀ η > 0, 1 ≤ M η) ∧ ∀ᶠ t : ℕ in atTop, ∀ p N, t≤N → ∀ (qt : store R.family d p t) {rt : ℝ},
      reads (C:=R.family) d N p t qt rt →
      ∃ x : R.family.label d, page (C:=R.family) d p t ((R.family.factory d N p).entries t x) =
          page (C:=R.family) d p t qt ∧
      (∀ other : R.family.label d, page (C:=R.family) d p t ((R.family.factory d N p).entries t other) =
        page (C:=R.family) d p t qt → other=x) ∧
      Charged R d N p t M (page (C:=R.family) d p t qt) x ∧
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
  obtain ⟨U,M,M1,labels⟩ := WilsonCapturedReturnedLabel.purchased R hG d
  refine ⟨M,M1,?_⟩
  filter_upwards [WilsonCapturedOriginalCrossing.purchased R d hG hγ hγ' he he',
    Filter.eventually_ge_atTop U] with t use Ut
  intro p N tN qt rt paid
  obtain ⟨x,coarse,stable⟩ := use p N tN qt paid
  obtain ⟨other,_,unique,full⟩ := labels t Ut N p tN (page (C:=R.family) d p t qt)
  have one : x=other := unique x coarse
  subst other
  exact ⟨x,coarse,unique,full,stable⟩

end YM.Integration.WilsonCapturedReturnedCrossing
end
