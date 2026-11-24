import YM.FVAAlt2.Rocket.Stamps
import YM.FVAAlt2.Shop.Lobby
/-! # Tell the Wilson-IR cover softening exactly which inputs (independently priced)
      at which order. The FAMILY OF LOCATIONS bought, no near-field exclusion except
      for instantiating the later atlas. Native units. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Kick
open Set Filter MeasureTheory Function Finset
open PertExtension Series Series.Radial Series.Tested Chart Orb
open Budget Budget.Tariff Budget.Premium Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Spatial
open Binding Diagram.Formal Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace
open Lattice Gauge Geometry Geometry.Field Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Halo Halo.Sight Gain Profiles
open Labels Source
open YM.FVAAlt2 YM.FVAAlt2.Fixed
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{X I:Type}{u a b p d:ℕ}{n:Side}{L: Meter X}{F:Frames G}{H:Hol G} (R:Lobby.Registry F H)
local notation "K"=> Foot G
variable (s₁:Finset I) (k:I→ℕ) (v:(j:I)→(F.level (k j)).Index) (z:I→Cover)
def topPortrait (z:I→Cover): Portrait G:= ∏ i∈s₁,convey (z i) (Profiles.bare (R.use (k i)) (v i))
def topMark (n:Side) (y:I→ Cover): Wilson.Config G n→ℝ:= ∏ i∈s₁,SlotEvaluation.fieldAt (R.use (k i)) (v i) (wrap n (y i))
def depthF (s₁:Finset I)(k:I→ℕ) (v:(j:I)→(F.level (k j)).Index) := ∑ j∈s₁,((F.level (k j)).grades (v j)).2
lemma top_lifted (f:Side)(t:ℝ)(x:spins G f): vital f (topPortrait R s₁ k v z) t x 1 = topMark R s₁ k v f z (Orb.liftLinks x):=by
 have h(t:Cover): translate t (orbLift x ∘ around f)= Lattice.expandAt (wrap f t) (Orb.liftLinks x):=by ext1 e; change orbLift x (wrap f (e.1+t),e.2)= orbLift x (_,e.2); rw [map_add]
 unfold vital topPortrait topMark; simp_rw [Finset.prod_apply]; apply prod_congr rfl; intro i _; unfold convey; rw [h]; rfl
open YM.FVAAlt2.Fixed Precision
local notation "n'"=> depthF s₁ k v
lemma top_truth [LinearOrder I] {D: ChartRatio G}(hD:LocalRatio D)(hn:Pert.Orb.Admissible n) {T:Orders (Foot G)} (hT: BasisT n' n' (topPortrait R s₁ k v z) T)(hx:Ranks n' T):
   plotPT Clocks.flat (vital n (topPortrait R s₁ k v z)) n'= Fixed.treeMom D (topMark R s₁ k v n z) n':=by
    have he:= even_iff_two_dvd.mpr hn.2; let O:= topMark R s₁ k v n z; let P:=vital n (topPortrait R s₁ k v z); let T₁(t:ℝ):= t⁻¹^ n'*Orb.preExpectation O t
    have hp : Clocks.flux Clocks.flat n n' (topPortrait R s₁ k v z)=T₁:=by
        funext u; unfold T₁ Clocks.flux goal; congr 1;
        have ht : rightSum (startO Clocks.flat) P u=preNum O u:=by
           unfold rightSum preNum; apply MeasureTheory.integral_congr_ae; filter_upwards with x; rw [Binding.head]; unfold Laplace.tilt; rw [show P u x 1= _ from top_lifted R s₁ k v z n u x]; unfold startO Clocks.flat; rw [one_mul]; rfl
        have hs : rightSum (startO Clocks.flat) (1:Hook G Empty (OEdge n)) u= preNum (G:=G) (n:=n) 1 u:=by
           unfold rightSum preNum; apply MeasureTheory.integral_congr_ae; filter_upwards with x; rw [Binding.head]; unfold Laplace.tilt startO Clocks.flat; dsimp only; rw [one_mul];rfl
        rw [hs,show rightSum _ _ _= _ from ht]; rfl
    letI: Module.Free ℝ (SchemeRG11.Sway.Land G n):= Module.Free.of_divisionRing ℝ (SchemeRG11.Sway.Land G n)
    let A:= Module.finBasis ℝ (SchemeRG11.Sway.Land G n);let B:= Module.finBasis ℝ (YM.FVAAlt2.ScalarGhost G n)
    have h:=Clocks.aspClock Clocks.flat ⟨_,_,hT,hx⟩ he; rw [hp] at h
    have hi:Aspiration T₁ (treeMom D O n') := Fixed.preExpectation hD A B s₁ hn (fun i:I=> YM.FVAAlt2.Shop.field_ok (R.use _) (v i) (R.owns _) (R.bid _) (wrap n (z i))) (fun i _=> Complex.continuous_re.comp ((R.use (k i)).continuous_places _ _))
    convert h.unique hi using 1; funext i; rw [term,Clocks.lampF,coeff_mk]
lemma dispatch {x:X→Room}(z:X→I→Cover)(hw:∃ y,Nearest x L y)(ht:∀ i∈s₁,Nearest x L (fun j=>z j i)): ∃ w:X→ Orders K, Kick L x (depthF s₁ k v) (fun j=> topPortrait R s₁ k v (z j)) w:= hands hw s₁ (fun i j=>z j i) _ (fun j=>((F.level (k j)).grades (v j)).2) (fun i _=> Profiles.authentically (R.use _) (R.owns _) (R.bid _) (v i)) ht
end YM.RegulatorIR.FVAAlt2.Kick
