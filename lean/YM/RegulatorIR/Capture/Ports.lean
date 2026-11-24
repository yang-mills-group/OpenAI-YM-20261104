import YM.RegulatorIR.Capture.Identity

/-!
# Conditional comparison internal Finite-top Port

No extrapolation of an actual correlation and no pos operation yet. Rates
before Frame normalization and budgets on phase adapters (not a CF result).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Capture
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{C D J':Choice M}
variable {S:Heir n G} (R:Reel S)(T:S.Accounts)
variable {m d: I→ℕ}
variable {F:∀ i,Labels.Frame G (d i)}{H:Hol G}
variable (Z: (i:I)→ Fabric R (F i) H) (Φ: (i:I)→ W → PhaseTests (d i))
variable {V: I→W→Set Room}{d':W→ℝ}{σ:I→ℝ}
variable {Γ:Flap M→Layer (Foot G) (Foot G)} {V': Flap M→Bride G} {c:Flap M→ℝ≥0∞}{γ:ℝ}

variable (J:Composite I) (K:Envelope Φ V d' L m J)(P:Passage R)(N: Lantern S D L c γ)(G₀: SchemeBeam R T Γ V' L c p k) (Yζ:∀ i,J.In i → S3 R T (Z i) D L p (m i) (tileC (plusU b u) a) (σ i)) (hm:0≤J.loss σ)(hb:0<b)(hk:transitK b u a≤ k)(Y₀:R.Endings L)

lemma Stocked (S': Milieu S T k p L):∀ y t,Nonempty (Store (fun x=> (principal J (Stall R Z Φ T)).main (leafX y x)) (Metric.closedBall 0 t) p):=fun _ _=> Store.flow S' (fun w=> mighty T J w fun i _=> fits R (Z i) (Φ i) w) _
include G₀ P
-- replicate same continuous-shift argument instantiated with Stroke/K profiles.
lemma radiant : ∀ y x t,swing (principal J (Stall R Z Φ T)) y x t:=by
 have he (J:Composite I) : CenterE (drawing J (CorpsUp R Z Φ)) S:=by
    induction J with
    | atom i=> exact sunny R (Z i) (Φ i)
    | pair A B ih ih'=> intro w t x; exact congr_arg₂ (·*·) (ih w t x) (ih' w t x)
 exact periodic _ _ P G₀.rates.run G₀.port (he J) (inaugural J _ _ (fun i _=> spoken R T (Z i) (Φ i)))

include K N Yζ hm hb hk Y₀

lemma ready (ht:J.accounts d≤a) : Seated S T (principal J (Stall R Z Φ T)) R.feeMarg L u b 6 p (J.accounts d) 1 γ c D:=by
 have hs:= chants R T Z Φ J K P N G₀ Yζ hm; have hh:= glare Φ J K
 exact seated R T J G₀ hs hh N hb hk ht Y₀

theorem funds (ht:J.accounts d≤a) (he:e ≤p)(hA:D.age≤C.age)(hl:C.age≤J'.age) :∃ K:ℝ,∃ t:ℕ,0≤K∧∀ w,
 ‖Profiles.score R J (CorpsUp R Z Φ) d e w - grouped R T (principal J (Stall R Z Φ T)) C J' w e‖≤ K * (L.val w).toReal^t * (S.modifyErr (J.accounts d) b γ J' w+S.l (J'.choose w)/S.P w):=by
 simp_rw [coherent R T _ C _ hl G₀.milieu (Stocked R T Z Φ J G₀.milieu) (radiant R T Z Φ J P G₀) he]
 exact paid_cells R T J G₀ (chants R T Z Φ J K P N G₀ Yζ hm) (glare Φ J K) N hb hk ht Y₀ he (le_trans hA hl) (fun i _=> steered R T (Z i) (Φ i)) (fun i _=> sunny R (Z i) (Φ i)) P
-- laws inspect scopes; normalization/clock posts
end YM.RegulatorIR.Capture
