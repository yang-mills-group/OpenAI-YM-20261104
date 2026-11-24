import YM.Integration.WilsonThermometerOwnOffsetNectar
import YM.MergeProof.ChaletS

/-! The original separated multisource integral for the normalized own-offset
columns, including every prior mixed face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOwnOffsetJoint
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetNectar
open scoped Classical BigOperators
set_option quotPrecheck false
variable {G : Gauge} (R : Run G) {N p k d : ℕ} {I : Type}
variable (z : I → Site (R.family.side N p)) (y : I → Palette R.family d)
  (V : I → Sight R.family d p) (r : I → Emblems R.family d)

def columns (j : ℕ) (i : I) := state (k:=k) R (V i) (r i) (y i) (z i) j
def origins (j : ℕ) (i : I) := location R (z i) j
def raw (hk : k≤N) (i : I) :=
  WilsonThermometerOwnOffsetNectar.birth R
    ((R.family.factory d N p).terminal (finer (r i) hk (y i) (primaryLetter d))) k (z i)

local notation "Q" => columns (k:=k) R z y V r
local notation "O" => origins R z
local notation "f" => (fun j i=>(Q j i).2.1)
local notation "g" => (fun j i=>(Q j i).2.2)
local notation "β₀" => R.alloy.B.a
variable {B : ℕ→ℕ→ℝ}
  (H : ∀ i, Enrolled R.makes R.doors B k N p d (digits R N p (z i)) (V i) (r i))
  (awake : Awake (C:=R.family) R.doors B k d) (simple : G.Simple) (hk:k≤N)
  (w : ℕ→I→ℝ) {u : ℝ} (test : Cap (d+2) (line (primaryLetter d)) u)

include awake H simple test
theorem accepted (i : I)
    (top : w N i * (‖factor R k N d‖ * (u * size (finer (r i) hk (y i)) *
      pricesTop (fly β₀) (far β₀) N d)) ≤ far β₀ N)
    (stages : ∀ j (hj:k≤j) (_:j<N),2*w (j+1) i*charge R (r i) (y i) hj u ≤ 1)
    (funded : ∀ j (hj:k≤j) (_:j<N),w (j+1) i*charge R (r i) (y i) hj u ≤ 1) :
    Nectar R.family.path (far β₀) R.doors p N k O w f g (raw R z y r hk) i := by
  have starts (e : ℕ) (he:e≤d) := (awake.post e he).trans hk
  have topRow := upper R (H i) simple hk starts (y i) test
  have safe (j : ℕ) (hj:k≤j) (hn:j≤N) := live R (H i) hj hn (y i)
  have next (j : ℕ) (hj:k≤j) (hn:j<N) := paid R (H i) awake hj hn (y i) test
  refine ⟨fun j hj hn=>(safe j hj hn).normK,?_,?_,?_,?_⟩
  · intro U
    exact (congrFun (written R (H i) hk starts (y i)) U).symm.trans ((congrFun (safe N hk le_rfl).read U).symm)
  · obtain ⟨F,hF,shown⟩ := topRow.2
    exact ⟨F,_,hF,top,shown.symm⟩
  · intro j hj hn
    obtain ⟨S,hs,c,_,proof⟩ := (next j hj hn).pays
    exact ⟨S,c,_,_,hs,stages j hj hn,funded j hj hn,proof⟩
  intro j hj hn
  have step := (next j hj hn).exactStep
  rw [one_smul] at step
  exact (safe j hj hn.le).read.trans (step.trans (congrArg ((R.family.path.levels.clock.op j p).push _) (safe (j+1) (hj.trans j.le_succ) hn).read.symm))

variable [Fintype I] [DecidableEq I] (names : Census I)

def density (hk : k≤N) {j:ℕ} (hn:j≤N) : Config G (R.family.side j p) → Poly names :=
  gust R.family.path N p N (MergeProof.Accent.birth names (R.family.path.rep N p N)
    (raw R z y r hk)) j hn

include awake H simple test
theorem issued
    (geometry:Matchup R.family.path (mutt β₀ R.Q) (renal β₀) p N k O w names)
    (top : ∀ i,w N i * (‖factor R k N d‖ * (u * size (finer (r i) hk (y i)) *
      pricesTop (fly β₀) (far β₀) N d)) ≤ far β₀ N)
    (prices : ∀ i j (hj:k≤j) (_:j<N),2*w (j+1) i*charge R (r i) (y i) hj u ≤ 1) :
    ∀ j (_hj:k≤j) (hn:j≤N),
      Integrable (density R z y r names hk hn) (prior G _) ∧
      (∀ i,(fun U=>(density R z y r names hk hn U).part (names.fire i))=
        Accent.manifest R.family.path p N f g j i) ∧
      Served (R.family.path.rep N p j) (f j) (Accent.tapes R.family.path p N g j)
        (density R z y r names hk hn) (O j) (w j) (topPitch R.family.path N j) 1 := by
  let joint := raw R z y r hk
  have hCont (i : I) : Continuous (joint i) := by
    change Continuous (fun U => ((R.family.S.a k:ℂ)^d) • R.family.O N p _ (z i) U)
    exact (R.family.continuousO N p d _ (z i)).const_smul ((R.family.S.a k:ℂ)^d)
  have actual : Continuous (R.family.path.rep N p N).eval := by
    have starts : (R.family.path.rep N p N).eval = bare (R.family.beta N p) := (R.makes.wilson.starts N p).2
    rw [starts]; exact bare_cont _
  have integrableStart : Integrable (Accent.birth names (R.family.path.rep N p N) joint) (prior G (R.family.side N p)) := (hatCont R.family N p joint hCont actual names).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have arms (i:I) := accepted R z y V r H awake simple hk w test i (top i) (prices i)
    (fun j hj hn=> by
      have nonneg := (paid R (H i) awake hj hn (y i) test).nonneg
      have positive := (geometry.pos (j+1) (hj.trans j.le_succ) hn i).le
      nlinarith only [prices i j hj hn, mul_nonneg positive nonneg])
  apply sentry R.family.path (mutt β₀ R.Q) (renal β₀) (far β₀) R.doors p N O w f g joint
    R.makes.wilson hk geometry (R.again simple).1.scrim.costs.night arms
  · intro j _ hn;exact gust_step _ _ _ _ _ hn
  · exact gust_base ..
  unfold density; rw [gust_base];exact integrableStart

end YM.Integration.WilsonThermometerOwnOffsetJoint
end
