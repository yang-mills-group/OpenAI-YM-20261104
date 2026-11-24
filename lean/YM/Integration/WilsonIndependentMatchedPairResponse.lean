import YM.Integration.WilsonIndependentMatchedResidualReading
import YM.RegulatorIR.Capture.Ports

/-! A designated source retains its gain into the complete normalized finite
correlation, on the same test, same torus and same unmarked vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Capture.MatchedPairResponse
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I:Type}{M:W→ℕ}{n:Page M→Side}{D:Choice M}{L:Meter W}
    {S:Heir n G}(R:Reel S)(T:S.Accounts){m d:I→ℕ}
    {F:∀i,Labels.Frame G (d i)}{H:Hol G}(Z:(i:I)→Fabric R (F i) H)
    (Φ:(i:I)→W→PhaseTests (d i)){V:I→W→Set Room}{d':W→ℝ}{σ:I→ℝ}
    {Γ:Flap M→Layer (Foot G) (Foot G)}{V':Flap M→Bride G}{c:Flap M→ℝ≥0∞}
    {γ:ℝ}{u b a p k e q:ℕ}
    (J:Composite I)(K:Envelope Φ V d' L m J)(P:Passage R)(N:Lantern S D L c γ)
    (beam:SchemeBeam R T Γ V' L c p k)(wage:∀i,J.In i→
      S3 R T (Z i) D L p (m i) (tileC (plusU b u) a) (σ i))
    (nonneg:0≤J.loss σ)(hb:0<b)(hk:transitK b u a≤k)(endings:R.Endings L)

include K P N beam wage nonneg hb hk endings

/-- Each occurrence pays the rooted gain of that very source. In particular,
a residual and its reflection can both carry a gain, with all mixed products
and intervening deposits inside the same normalized ordinary reading. -/
theorem original (room:J.accounts d+q≤a)(weight:J.loss σ≤q)(he:e≤p):
    Carry (L.us (film W ∘ introF S)) (fun v:Face S=>
      retainErr S (J.accounts d) b γ (fun w=>ENNReal.ofReal (S.ε w^J.loss σ)) v.val.1)
      (fun v=>‖reading S R.docket (fun i=>vital (n (Page.opening _ (film W i)))
        (drawing J (CorpsUp R Z Φ) i)) (J.accounts d) (introF S v) e‖ₑ) := by
  let book:=chants R T Z Φ J K P N beam wage nonneg
  let domain:=glare Φ J K
  let central:=seated R T J beam book domain N hb hk (by omega) endings
  have gain:=enhanced J (CorpsUp R Z Φ) (Stall R Z Φ T) (haloed R (film W) beam)
    book domain (lanterns (film W) N) hb hk room weight
  simp_rw [reading_top R T J beam book]
  exact YM.Integration.WilsonIndependentMatchedResidualReading.atCenter S T _ _ central _
    gain (fun _=>ENNReal.ofReal_ne_top) he

end YM.RegulatorIR.Capture.MatchedPairResponse
end
