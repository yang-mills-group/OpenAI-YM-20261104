import YM.Integration.WilsonIndependentFreshCopyLimit
import YM.RegulatorIR.Tape.Resound

/-! A freshly planted group word on a nonbare course satisfies the cover Ward
identity at every subsequent wing. The finite measures on the growing tori
are the original Wilson measures with their entire preceding quiet history. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonIndependentFreshCoverWard
open RegulatorIR
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding
open Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram
open Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG
open Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Sight
open Gain WilsonIndependentFreshCopyWage
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {W : Type} {M : W → ℕ} {n : Page M → Side} {S : Heir n G}
  (H : Reel S) (T : S.Accounts) (quiet : H.Follows T) (large : Common H)
  (E : Era M) {L : Meter W} {p k m s : ℕ} (B : S.Primitive L p k)
  (Z : (E.part S T B).Report m) (w : W) (bank : S.Supplies T L p k)
  (C : Aug.Amenities S L p k) (film : W → Portrait G)
  (stamp : ∀ w, BasisT m s (film w) (Z.main (Page.opening E.spans w)))
  (j : ℕ) (hj : j ≤ E.spans w) (hk : 14 ≤ k)

include stamp bank C quiet large hk in
theorem matched {X Y : (z : Side) → ℝ → Horizon G (big w n (Aug.sheet w (E.age w+j) (absAge E w hj) z))}
    {u v : Foot G → ℝ⟦X⟧}
    (P : Aria H w (E.age w+j) (absAge E w hj) X u (p := p))
    (Q : Aria H w (E.age w+j) (absAge E w hj) Y v (p := p))
    (same : ∀ z, reel_prop (X z) (Y z)) {e : ℕ} (he : e ≤ p) :
    rhymeR u (Z.main ⟨w,j,hj⟩) m e = rhymeR v (Z.main ⟨w,j,hj⟩) m e := by
  apply tendsto_nhds_unique (WilsonIndependentFreshCopyLimit.chorus H T quiet large E B Z w
    bank C film stamp j hj X u P hk e he)
  have other := WilsonIndependentFreshCopyLimit.chorus H T quiet large E B Z w
    bank C film stamp j hj Y v Q hk e he
  convert other using 1
  ext1 z
  exact congrArg (fun y : ℝ⟦X⟧ => coeff e y)
    (WilsonIndependentFreshCopyRange.observed H T quiet large E B Z film stamp w
      (sheetAt E w j hj z) (X z) (Y z) (P.rays z) (Q.rays z) (same z))

variable {J : Flap M → Layer (Foot G) (Foot G)} {V : Flap M → Bride G}
  {c : Flap M → ℝ≥0∞} (A : Azur H J V k L c) (inspiration : Inspires J V S)
include stamp bank C quiet hk A inspiration in
theorem original (wing : Flap E.spans) (i : ℕ) (hi : i ≤ p) :
    (S.sight (E.wing wing)).Way (Z.main wing.prev) i := by
  obtain ⟨w,j,h⟩ := wing
  let wing : Flap E.spans := ⟨w,j,h⟩
  let original := E.wing wing
  let F := Z.main wing.prev
  let grid := S.sight original
  have cap : Ranks m F := Z.cap_b (fun a => essential H (E.wing a)) _
  have gross : Cluster.Bill F i := fun e he r =>
    WilsonIndependentFreshCopyLimit.cusp_b H T quiet A.run E B Z w bank C film stamp j h.le r e (he.trans hi)
  refine consents grid.straight grid.space F cap ?_ (A.packL inspiration original i)
    (A.pack inspiration original i) gross
  intro s' x e leq
  let t := Cluster.Brief.tile s'
  let z := dilute t x
  unfold grid
  rw [inspiration.tune original,setup,stylist]
  apply Eq.symm
  have enrolled := A.invoke original
  let f := basicB (J original) z
  let v := basicP (V original) z
  exact matched H T quiet A.run E B Z w bank C film stamp j h.le hk
    (Gain.ariaF f v H w (E.age w+j) (absAge E w h.le) p
      (basic_cov _ _ _ enrolled.costL) (basic_cost _ _ _ enrolled.costH))
    (Gain.ariaB f H w (E.age w+j) (absAge E w h.le) p (basic_cov _ _ _ enrolled.costL))
    (fun z' => current_event _ (Gain.dropV_tag z' (H.deep original.prev) v)) (leq.trans hi)

end YM.Integration.WilsonIndependentFreshCoverWard
