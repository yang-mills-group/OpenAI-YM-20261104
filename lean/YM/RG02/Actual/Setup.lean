import YM.RG02.Flat.First
import YM.RG02.Flat.Origins
import YM.RG02.Actual.Selected
import YM.Spec.Closed

/-!
# Bindings to producers

A sharing witness on the SAME C from the common ledger. H and roll data can
be extracted once from F.calibration; the calibration existence doesn't name
different resulting coefficient predictors on equivalent reroutes. Work up to
the admitted actual cutoff m≤N. No hypotheses on other existence projects or
a family at a different kernel penalty. This binds the reset test from the same
kinetic programs. Keep costs explicit even when input is re-expressed to
agreement only after further chamber resets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02
open Filter Function MeasureTheory Set Metric Lattice Wilson RG Precision Tree Supply Bid Marker Extra.Trajectories
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Therm Asym Tangent Grade PowerSeries Profiles
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}{I : Type}[DecidableEq I][Fintype I]{B : Census I}

/-- History-indexed hypothesis to be used with one `actual.Physics`. -/
structure Along (H : History G) where
   s : RG.Supply.Sheet G
   q : RG.Supply.Rolls s
   η : ChartRatio G
   X : Precision.MapPrices
   prices : Precision.PostCost q
   M : Precision.Horizon H.levels
   V : Kin M η
   receipt : LocalRatio η
   suffice : M.Suffices X
   paid : V.Planned prices
   reads (N m p : ℕ) : m≤N→ (H.rep N p m).path= V.path N m
   angle (N m p : ℕ): m<N→ |H.β N p m-H.β N p (m+1)-V.alpha N m| ≤ 1

namespace Along
variable {C:Family G}

theorem sound (T : Spec.Calibrated C) : Nonempty (Along C.path) := by
   obtain ⟨S,D,T,W,Y,I,O,K,P,B,F,hB,hC,hF⟩:=T
   rw [hC]; refine ⟨S,D,O,K,P,B.M,B.kin,B.ratio,B.plan,B.support,fun N m p hm=>?_,fun N m p hm=>?_⟩
   · have h := ((hB N p).prices m (Nat.zero_le _) hm).1.path; rw [B.bases] at h; exact h
   exact (hF N m p hm).δ

-- Through-order analytic part at the actual trajectory. F.pose variables
-- retained as proofs; all producer endpoints allow arbitrary such choices
-- but don't assert uniqueness of all of `kin`. `βkin` only first correction,
-- not a claim that number is all needed.
variable {H : History G} (A : Along H) {N m p : ℕ}


theorem home (T : Forest (H.levels.clock.op m p).ratio)(hk : m<N) :
    let L:= H.levels
    let k := L.clock.J (m+1)
    let ρ := A.V.stationary N m p T
    let θ := (L.params (m+1)).clip
    let R := (H.rep N p (m+1)).path
    let η := A.prices.η k
    PriceGap T θ R η ∧ Critical T θ R ρ ∧
        Comptroller T (A.M.H N (m+1)) θ R ∧ Sworn (A.M.H N m) (L.S.side m p) G ∧
        Guessed T (Bloch.installed (H.levels.clock.op m p).ratio (A.M.towers N m).A0) ρ ∧ FiniteBound T R (H.rep N p m).path θ (L.params m).clip (A.V.alpha N m) A.η ρ (A.prices.Γ k) (A.prices.c k) (L.clock.loopCap (m+1)) := by
   intro L k ρ θ R η; unfold R θ k L ρ; rw [A.reads .., A.reads ..];
   · obtain ⟨u,v⟩ := A.paid.critical N m p hk T
     exact ⟨A.paid.gap N m p hk T, u,Orientation.certifies A.suffice A.paid p hk T, Orientation.oath A.suffice A.paid hk.le _,v,A.paid.retains N m p hk T⟩
   · exact hk.le
   exact hk

abbrev ζ (m : ℕ) := A.prices.η (H.levels.clock.J (m+1))
abbrev stone (N m : ℕ) := A.M.H N m
abbrev clip (H : History G)(m : ℕ) := (H.levels.params m).clip

lemma pricing (T : Forest (H.levels.clock.op m p).ratio)(hk : m<N) :
    PriceGap T (clip H (m+1)) (H.rep N p (m+1)).path (ζ A m) := (A.home T hk).1
lemma chooses (T : Forest (H.levels.clock.op m p).ratio)(hk : m<N) :
    Critical T (clip H (m+1)) (H.rep N p (m+1)).path (A.V.stationary N m p T) := (A.home T hk).2.1
lemma toll (m : ℕ) : 0< ζ A m := A.prices.price _

variable (T : Forest (H.levels.clock.op m p).ratio)(hk : m<N)
    (i : (H.levels.clock.op m p).Choices)(x : Dir G (H.S.side m p))(U : Fk.Space G (H.S.side (m+1) p)→ℝ)
    (k : ℕ)(W : Fk.Space G (H.S.side (m+1) p)→ Poly B)

def marked := Fk.Draw.formal T i (A.toll m) (A.pricing T hk) (A.chooses T hk) A.η x U k W

def fixed := Fk.Draw.multiplier T i (A.toll m) (A.pricing T hk) (A.chooses T hk) A.η x

include hk
theorem stationaryPrice :
    let Y := (A.V.stationary N m p T)
    let R := (H.rep N p (m+1)).path
    Tangent.crest T Y x=relative T (Bloch.installed (H.levels.clock.op m p).ratio (A.M.towers N m).A0) x ∧
    Tangent.due T i (clip H (m+1)) R x (Tangent.crest T Y x)= gaugeFiscal (A.M.H N m) x x/2 := by
   intro _ R; unfold R; rw [A.reads N (m+1) p hk]; exact Tangent.priced A.suffice A.paid hk p T i x

lemma constant (h : Fk.Ink k W) : basepoint (A.marked T hk i x U k W)=1 := Fk.Draw.configured T _ _ _ _ _ _ h
lemma stationaryPaid : 0< A.fixed T hk i x:= Fk.Draw.multiplier_pos T _ _ _ _ _ _ A.receipt

theorem steers (h : Fk.Ink k W)(hx : Fk.Ambient U) :
    let S:= H.levels.clock.op m p
    let θ := (H.levels.params (m+1)).clip
    let R := (H.rep N p (m+1)).path
    ∃ M∈𝓝 (1:T.Slice G), MeasurableSet M ∧ (∀ u∈M,YM.RG02.Branch.Inspected S (T.drape u)) ∧
     ∀ Y∈𝓝 (1:T.Slice G), MeasurableSet Y→ Y⊆M →
       (∀ᶠ t in Tested.germ,∀ s:B.Mode, IntegrableOn (fun u=> (Fk.through S θ R k W U x t u).part s) (Profiles.wick T ⁻¹' Y) (prior G _)) ∧
       Fk.Reading (A.marked T hk i x U k W) (A.fixed T hk i x) T A.η (fun t=> Fk.atSet S θ R k W U x t (Profiles.wick T ⁻¹' Y)) := by
    intro S θ R
    have Hc := A.home T hk
    have Hh : R= A.V.path N (m+1):= A.reads N _ p hk
    exact Fk.attained T i (A.toll m) (A.pricing T hk) (A.chooses T hk) (Hh.symm ▸ A.paid.cap N (m+1) hk) h hx (H.levels.blocks m p).branches A.receipt x (Hc.2.2.1)

lemma compatible (h : Fk.Ink k W)(hx : Fk.Ambient U)(T' : Forest (H.levels.clock.op m p).ratio)(j) :
    A.fixed T hk i x=A.fixed T' hk j x ∧ A.marked T hk i x U k W = A.marked T' hk j x U k W := by
   have hV := A.paid.cap N (m+1) hk
   exact Fk.Draw.independence T T' i j _ _ _ _ _ _ ((A.reads N (m+1) p hk).symm ▸ hV) h hx (H.levels.blocks .. |>.branches) A.receipt A.receipt x (fun T=>(A.home T hk).2.2.1)

end Along
end YM.RG02
