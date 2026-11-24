import YM.FVAAlt2.Rocket.Orbit
/-!
Universal cover calculator from primitive budgets. It runs for exactly the stencil list in
 `Calls`, gauge & fine tag fixed. Reconcile after the charges: κ ε (incl color bead), frames
 via deterministic ε. Older warmth comparison still required separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Labels Source Clocks
open Oracle Atlas Epoch Calibration Kick
open YM.FVAAlt2
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{u a b p r:ℕ}{M:X→ℕ}{n:Page M→Side}{G:Gauge}
variable (S:Oracle.Circuit M n){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P: Patch,P.Branches K G) {B:Epoch.Marked M}
variable {g:G.ColorIndex}{γ:ℝ}{c₀:ℝ}(F: Tent M){x:X→Room}{L:Meter X}
local notation "AΘ"=> S.payroll Y G Z (sheet F)
local notation "Σ'"=> S.dialect Y G Z (sheet F)
local notation "η"=> native M
local notation:max "P_" w:max => Page.opening M w
variable {L':Frames G}{H:Hol G} (R:Lobby.Registry L' H)[LinearOrder I]
variable (s₁:Finset I) (k:I→ℕ) (v:(j:I)→(L'.level (k j)).Index) (j:Choice M)
local notation "m"=> depthF s₁ k v
local notation "V"=> topPortrait R s₁ k v
lemma kicks0 (z:I→Cover): ∃ T, Halo.BasisT m m (V z) T ∧ Ranks m T:=by
    let L:= Meter.mk (W:=Unit) 1 (fun _=>le_rfl) (fun _=>ENNReal.one_ne_top)
    have hx (i:Cover):Nearest (X:=Unit) 0 L fun _=>i :=⟨Uniform.Poly.standard _ (u:= ENNReal.ofReal (dist (0: Room) (Motion.slide 1 i))) ENNReal.ofReal_ne_top⟩
    obtain ⟨T,hT⟩:= dispatch R s₁ k v (fun _=>z) (Exists.intro _ (hx 0)) (fun i _=> hx _); exact ⟨ T (),hT.authority (),hT.census _ ⟩
def kickStart (z:I→Cover): Orders (Foot G):= (kicks0 R s₁ k v z).choose
lemma kickLaw (z:I→Cover):Halo.BasisT m m (V z) (kickStart R s₁ k v z) ∧ Ranks m (kickStart R s₁ k v z):= (kicks0 R s₁ k v z).choose_spec
def Ignite (z:X→I→Cover) : (AΘ).Report m:= Profiles.declaring AΘ (fun w=> kickStart R s₁ k v (z w)) (fun w=> (kickLaw R s₁ k v _).2)
def stopped (z:X→I→ Cover)(w:X) (e:ℕ): ℝ:= note ((Ignite S Y Z F R s₁ k v z).main (j.choose w) e 0)
lemma stones (z:X→I→Cover)(ht:∀ i∈s₁,Nearest x L (fun j=>z j i))(hx:∃ y,Nearest x L y) : Kick L x m (fun j=>V (z j)) (fun w=> kickStart R s₁ k v (z w)):=by
     obtain ⟨Z,hZ⟩:= dispatch R s₁ k v z hx ht
     have he:Z=(fun w=> kickStart R s₁ k v (z w)):=funext fun i=> certifies (hZ.authority i) (kickLaw R s₁ k v _).1 (hZ.census i) (kickLaw R s₁ k v _).2
     rwa [he] at hZ
variable {D:Precision.ChartRatio G} (hD:Precision.LocalRatio D) (hq:Atlas.SatisfiesQ G Y S Z B p u γ) (hver:Notebook S Y G Z g (native M) F p) (hc:∀ w,B.peak (Page.opening M w)=0) (hP:∀ w,S.l (Page.opening M w)=1)
variable (hL:OfAge B L)(hN: ∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v) (hg:G.Simple) (hb:quantum 1 0 ≤u)(hp:0<c₀)(ht:(S.dialect Y G Z (sheet F)).cushion c₀ x)
def wage (ω₁:ℝ)(w:X): ℝ≥0∞:= ENNReal.ofReal ((Σ').modifyErr 0 1 ω₁ j w)
include hD hq hP hc hver hL hN hg hp hb ht
lemma soothe (z:X→ I→Cover)(hz:∀ i∈s₁,Nearest x L fun w=>z w i)(hx:∃ y,Nearest x L y)(e:ℕ)(he:e≤p) : Carry L (wage S Y Z F j γ) fun w=> ‖ YM.FVAAlt2.Fixed.treeMom D (topMark R s₁ k v (n P_ w) (z w)) m e - stopped S Y Z F R s₁ k v j z w e‖ₑ:=by
    have H:= stones R s₁ k v z hz hx; have hv := start_table (e:=e) S Y Z _ H hq hver hc hP hL hN hg j hb hp ht he
    have hx(w:X): Pert.Orb.Admissible (n (P_ w)):= ⟨S.stands _, even_iff_two_dvd.mp (S.dual _)⟩
    simp_rw [fun w=> Kick.top_truth R s₁ k v _ hD (hx w) (H.authority w) (H.census w)] at hv; exact hv
end YM.RegulatorIR.FVAAlt2.Rocket
