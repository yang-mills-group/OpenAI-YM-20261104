import YM.RegulatorIR.Sources.Child

/-!
# Independent rooted single mark graph

Canonical h-preserving matrix tunings supply root bounds when initialized in
`Tap` columns. This definition does NOT evaluate tests on a common k-grid;
it averages CHILD mark rec with actual distinct pulled tests in root units.
Recover full tested insertion including pre-factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Sources
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered Labels Source Aperture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W J X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
variable {S:Heir n G} (R:Reel S)(T:S.Accounts)
abbrev display (x:Side):ℝ:= x.val
variable {F:Labels.Frame G d}{H:Hol G}

structure Fabric (R:Reel S)(F:Labels.Frame G d)(H:Hol G) where
 A: SectionData F
 origin : A.Sound H
 can : Bid.pop A
 accent : W → Feeds
 tune :∀ w,R.clock (Page.opening M w)=(accent w).scale
 tap : W→Tap F
-- accelerate root data

namespace Fabric
variable {R} (Z: Fabric R F H)
def readB (w:W)(x:Room)(φ:PhaseTests d): Portrait G:= Testifies φ (Z.tap w) Z.A (Z.accent w) (S.ε w) x
def drawnU (w:W)(x:Room)(φ:PhaseTests d): Orders (Foot G):= spineV Z.A Z.origin Z.can φ (Z.tap w) (Z.accent w) (S.ε w) x
lemma depicts (w x φ) : Halo.BasisT d d (Z.readB w x φ) (Z.drawnU w x φ)∧ Ranks d (Z.drawnU w x φ):= selling ..

-- additional path homographies: translation orientation
lemma eases (w:W)(i:Stroke F)(s:Cover): rebaseO s (shape Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i 0)= shape Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i s:=by
 let P:=shape Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i; let α:=planet Z.A (Z.tap w) (Z.accent w) i
 have hv z: Halo.BasisT d d (α z) (P z) ∧ Ranks d (P z):= (stamp_symbol (landed Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i z)).choose_spec
 have ht : convey s (α 0)=α s:=by ext1 t; ext1 x;change fees _ _ _ _*bare _ _ _ (translate 0 _)=_; rw [show translate 0 (translate s x)=translate s x from ?_]; rfl; ext1 p;simp [translate]
 have hh: Halo.BasisT d d (α s) (rebaseO s (P 0)):=ht ▸ ((hv 0).1.vayne s); apply certifies hh (hv s).1 (fun j r he=>(hv 0).2 j r (fun hg=>he (by rw [rebaseO,hg,echo_zero]))) (hv s).2

def beginsV (w:W) (φ:Room→ℝ) : Orders (Foot G) := ∑ i:Stroke F, derivativeA i φ 0 • shape Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i 0
-- root stencil in native units; carrier X allows wild tests but supplies only smooth class. output relative root at center. No terminal Gamma yet. In the finite-RG prescription compute in this history.
end Fabric
variable (Z: Fabric R F H)
def Sample (F: Type): Type:= (Room→ℝ)→ Orders F
def tally (L:Side)(m:ℕ):ℝ:= (display L)^m/(display L)^4
def sprink (w:Flap M)(v: Sample (Foot G))(m:ℕ): Sample (Foot G):=by
 let L:=(R.steps w).patch.L; exact fun φ:Room→ℝ=> tally L m • ∑ i: Site L, (S.frames w).each m (T.bulk w.prev) (rebaseO (Lattice.lift i) (v (calling L φ i)))
-- gauge identity costs not in this module

def pyramid : Page M → Sample (Foot G):= Halo.seriesC (X:=fun _=> Sample (Foot G)) (fun w=> Z.beginsV w) fun w v=> sprink R T w v d
lemma swimP (w:W): pyramid R T Z (Page.opening M w)= Z.beginsV w:= Halo.earlierC w
lemma sweepsP (w:Flap M):pyramid R T Z w.next=sprink R T w (pyramid R T Z w.prev) d:= Halo.laterC w

-- evaluated any physical-center test at common $λ_i$. Unit multiplier at
-- coarse before reexpression. Costs match tested root estimates.
variable (Φ: W→ PhaseTests d)

def softL (l:ℝ)(d:ℕ):= l^4/l^d
def sparks (w:Page M)(x:Room)(v:Cover): Orders (Foot G) := softL (S.l w) d • rebaseO v (pyramid R T Z w (perch (Φ w.bindW).phi (S.l w) x v))
lemma restore_start (w:W) x v:sparks R T Z Φ (Page.opening M w) x v= ∑ i:Stroke F,partV Z.A Z.origin Z.can (Φ w) (Z.tap w) (Z.accent w) (S.ε w) x v i:=by
 let y:= slide (S.ε w) v-x;let t:= S.ε w; let ψ:= Φ w
 unfold sparks; rw [swimP, Fabric.beginsV, echoes_sum, Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _;rw [echoApply, Z.eases w, smul_smul]
 apply congr_arg (fun z:ℝ => z • _); unfold derivativeA;change softL t d*iteratedFDeriv ℝ (nu i) (gaze ψ.phi t y) 0 (finger i)= _
 rw [beamAt ψ.smooth (le_trans (Nat.le_add_left ..) (combo i))]; simp only [smul_zero,add_zero]; rfl
lemma refundP (w:Flap M): softL (S.l w.next) d* tally (R.steps w).patch.L d=softL (S.l w.prev) d:=by
 unfold tally softL; let s:= display (R.steps w).patch.L; have hx: s≠0 := by unfold s display; positivity
 rw [scaledCard R]; change (S.l w.prev*s)^4 / (S.l w.prev*s)^d*(s^d/s^4)= _; rw [mul_pow (S.l w.prev) _ d];field_simp
variable (K: Passage R)(A₀: Common R)(H₀:R.Follows T)
include K A₀ H₀
lemma restore_step (w:Flap M)(x:Room)(v:Cover): sparks R T Z Φ w.next x v=∑ i:Site (R.steps w).patch.L,(S.frames w).each d (T.bulk w.prev) (sparks R T Z Φ w.prev x (child (R.steps w).patch.L v i)):=by
 let J:= (S.frames w).each d (T.bulk w.prev); let s:= softL (S.l w.prev) d;let D:=(R.steps w).patch.L;let U:= pyramid R T Z w.prev;let φ:=Φ w.volW
 rw [sparks, sweepsP, sprink,echoApply, echoes_sum, smul_smul, refundP, Finset.smul_sum]
 apply Finset.sum_congr rfl;intro i _; change s • rebaseO v (J (rebaseO _ (U (calling D (perch φ.phi (S.l w.next) x v) i))))= J _
 rw [twig R w φ.phi x v i, eachRebase R K A₀ H₀ _, sparks,rootR]; exact (homogenous s (S.frames w) (T.bulk w.prev) (m:=d) (rebaseO _ _)).symm

omit K A₀ H₀
variable (G₀:Milieu S T k p L)
include G₀
lemma shapeB (w:Page M) (φ:Room→ℝ) : Cluster.Bill (pyramid R T Z w φ) p:= by
 suffices h: ∀ w:Page M,∀ a:Room→ℝ,Cluster.Bill (pyramid R T Z w a) p from h w φ
 refine Page.proves ?_ ?_
 · intro w φ;rw [swimP]; apply sigmaPrice _; intro i _; apply scalePrice; intro e _ r; exact Prim.bound_cost (((stamp_symbol (landed Z.A Z.origin Z.can (Z.tap w) (Z.accent w) i 0)).choose_spec.1).canopy e r)
 intro w h φ;rw [sweepsP]; unfold sprink; exact scalePrice (sigmaPrice _ (fun i _=> estimateM (m:=d) G₀ w (echoBill (Lattice.lift i) _ (h (calling _ φ i))))) _
lemma sparkCost (w:Page M)(x:Room)(v: Cover): Cluster.Bill (sparks R T Z Φ w x v) p:= scalePrice (echoBill _ _ (shapeB R T Z G₀ w _)) _
end YM.RegulatorIR.Sources
