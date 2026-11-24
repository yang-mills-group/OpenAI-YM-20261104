import YM.RG04B.Start.Clock
import YM.RG04B.Relay

/-!
# **Issued** on the actual common history: full-order startup vacuum supply

No compatibility or Clip premise missing here: derive from T in UV. Keep
scalar, forced partners and period data. Its use on actual density uses
`Remodeled` (the denominators on that history). Unmasked interpretation
`prescribed`, `rank_sum`, `vacant`: evaluation at actual beta of additional
Taylor packets of Wilson germ through r+2 in link fluctuation jets. The Fk
recursion's higher-block outputs (independent predictive side) remain to be
supplied in THAT convention; startup owes no loop kernel from a different
prescription. Stronger local K reserves than the actual inherited w/mass at
this receipt would require additional booking and payments (not asserting).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B.Startup
open Function Filter RG Lattice Wilson Real RG.Supply
open PhysicalNext Repeat Legato Tent
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {R : Run G} (T : Campaign R)

set_option quotPrecheck false
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "F" => R.family.path.levels.clock
local notation "S" => R.family.path.levels.params
local notation "A!" => R.family.path.rep

include T
private lemma startupRep (N p : ℕ) : (A! N p N) = launch (A:=R.alloy) N p ((A! N p N).beta) :=
  (T.center N p).startStory T.gains

lemma pathFact (N p : ℕ) : (A! N p N).path = WilsonStartup.Design.top G (A! N p N).clip := by
  have h:= startupRep T N p
  rw [h]
  exact T.gains.Lead _

/-- The high-order top packets & their weighted error at *every* sufficiently
fine start, all volumes; no assumption of already starting in high-order cone. -/
theorem issues (h : Booked (temperatures G) P) (r : ℕ) {ε δ : ℝ} (he : 0 < ε) (hd : 0 < δ)
    (hr : 2 ≤ r) : ∀ᶠ N : ℕ in atTop,
      ∀ p : ℕ,
        let X := A! N p N
        let v := chart G ((C).side N p) X.clip X.beta (r+2)
        let Q := {X.activities with E:=X.activities.E-v}
        Remodeled C N p N X ∧ X.eval=Wilson.bare X.beta ∧ X.v=0 ∧
        X.path = WilsonStartup.Design.top G X.clip ∧
        Q.RegularFamily X.p ∧ Q.EBound X.p (δ*(gAt C N p N)^((r:ℝ)+1-ε)) := by
  filter_upwards [pre_cost R.makes T.gains.SimpleR h r ε δ he hd] with N hp p
  let x := A! N p N
  have ht:x= launch (A:=R.alloy) N p x.beta:= startupRep T N p
  have ha:x.p=(P|>.budget N):=(R.makes.wilson.represents N p N le_rfl).vac
  have hc: x.clip.direct ≤ 1 := by
    -- metric from paths
    exact Push.PriceCompiler.Canonical.direct_le_one (R.makes.wilson.represents N p N le_rfl|>.good.paths.metric)
  obtain ⟨hl,hk⟩:=hp _ p le_rfl
  have hv:x.p.threshold ≤ required G (r+2) x.p.order x.p.power:= ha.symm ▸ hl
  intro X v Q
  have hg := beta_positive R.makes N p N le_rfl
  refine ⟨staying R.makes N p N le_rfl,(R.makes.wilson.starts N p).2,(R.makes.wilson.starts N p).1,pathFact T N p,?_⟩
  suffices H: Q.RegularFamily x.p ∧ Q.EBound x.p (cost G ((P).budget N) ((A! N p N).beta) (r+2)) by
    obtain ⟨hi,b,hb,h⟩:=H; exact ⟨hi,b,hb,fun i=> Push.AbsoluteSums.budget_loosen (h i) hk⟩
  rw [← ha]
  -- stencil definition after ht; avoid recursive rw under beta
  let B := ((A! N p N).beta)
  let X':= launch (A:=R.alloy) N p B
  change Q.RegularFamily x.p ∧ Q.EBound x.p (cost G x.p B (r+2))
  have hβ : X.beta=B:=rfl
  have heC : X.clip=(S N).clip:=(R.makes.wilson.represents _ _ _ le_rfl).clip
  have hpat : X= X':=ht
  unfold Q v; rw [hβ,heC,hpat]
  change _ ∧ _
  rw [ha]
  apply deployed (show (S N).clip.direct ≤ 1 from heC ▸ hc) (by omega) (ha ▸ hv) B (Real.norm_of_nonneg hg.le|>.le)
end YM.RG04B.Startup
