import YM.FVAAlt2.Pipeline.Readers
import YM.FVAAlt2.Pipeline.Near
/-!
# One cover & periodic formal history. Chronology.

Along same path proving invariance through all finite standards w.r.t analytic representative choice of formal resets under jet agreement (supplied, through overlap across co-admissions and Y.Art via Neighborhoods). Need not, e.g., appoint one entire analytic beta with those jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline.Hours
open Function Set Filter MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth Arm Crown
open Lattice RG Precision Comparison.RG02.Bulk Oracle Circuit Step See Clocks
open PowerSeries
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
open Period.Field
variable {G:Gauge}{X:Type} {Q:KernelChoices}{M:X→ℕ}{N:Page M→Side}{Γ: History G}{m r:ℕ}
variable {C:Circuit M N}(Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (K: Comparison.RG02.Bulk.Chain Γ)(P: SeriesT C Q Γ)
variable (L L':Page M→Binding.Scale)
variable (A A': X→ Boot.Scout (G:=G) m) (p:ℕ) -- period
local notation:max "U_" k:max=> P.stepData C Γ p k
local notation:max "F_" k:max=> Halo.bios ( P.stepData C Γ p k )
local notation:max "K_" k:max=> ( P.readyKin C Γ K p k )
local notation:max "f_" i:max=> ( Γ.S.side ( P.vol i ) p )
local notation "G₀"=> ( C.payroll Y G Φ L )
variable {L L' A A'}
variable (h:∀ w:Page M, Ward.Squares r (tale ( L w ).beta) (tale (L' w).beta))
lemma match_send {X Y :Type}{v w:Orders X}(h:Matches r v w)(i:X→Y) : Matches r (sendL i v) (sendL i w):= by intro j hj; unfold sendL; simp_rw [h j hj]
include h
lemma events (i:Flap M) (w): Matches r ( C.bore G Φ L i w ) ( C.bore G Φ L' i w ):= prism_now (C.rail Q i) (C.rail Q i) (L i.prev) _ rfl rfl (Φ (C.pactP i)) (C.wheeled G Φ L i) (C.wheeled G Φ L' i) (h _) w
lemma held (i:Flap M) (n p:Side): Matches r (Booth.studied ( C.bore G Φ L i ) n p) (Booth.studied ( C.bore G Φ L' i ) n p):= by intro j hj; simp_rw [Booth.studied, Finset.sum_apply]; exact Finset.sum_congr rfl fun w _=> match_send (events Φ h i (traverse p n w)) _ j hj
lemma topV (x:X)(P':Side):Matches r (Boot.weights (Circuit.mural G L x) P') (Boot.weights (Circuit.mural G L' x) P'):= by intro j hj; simp_rw [Boot.weights,Finset.sum_apply]; exact Finset.sum_congr rfl fun w _=> match_send ( Clocks.stageM (Circuit.serene G L x (Boot.pinto w)) (Circuit.serene G L' x (Boot.pinto w)) (fun z=> Clocks.plain_agree _ _ (h _) z (Boot.pinto w)) ) _ j hj
omit h
lemma lettering (i:Flap M){x y: StockT P p i.prev}(hs: Matches r x y): Matches r (Recv P p i x) (Recv P p i y):= See.transferred (X:= fun i:ℕ=>Orders (Pin (Γ.S.side i p) G)) (Y:= fun i:ℕ=>Orders (Pin (Γ.S.side i p) G)) (fun i:ℕ=> Clocks.Matches (I:=Pin (Γ.S.side i p) G) r) x y (P.links i) hs
include h
set_option quotPrecheck false
section Film
variable (i:Flap M){x y:StockT P p i.prev}(hs: Matches r x y)
local notation "q"=> (Γ.S.side (P.vol i.next+1) p)
local notation "ξ" => Arm.layerSet ( U_ i ) ( C.bore G Φ L i ) (Recv P p i x)
local notation "θ" => Arm.layerSet ( U_ i ) ( C.bore G Φ L' i ) (Recv P p i y)
include hs
lemma priceHx : Matches r (ξ) (θ):= by
    intro j hj; ext1 z; unfold Arm.layerSet Binding.supply; simp_rw [Pi.add_apply,Cluster.present,lettering P p i hs j hj,held (C:=C) Φ h i _ _ j hj]
lemma predict : Matches r (riseV Φ K P L p i x) (riseV Φ K P L' p i y):= by
    let L₁:= Arm.spins ( U_ i ) ( F_ i ) ( K_ i ); intro j hj; ext1 z; unfold riseV Arm.OutputV Binding.pulp; split
    · rfl
    unfold Arm.scriptV collectO; congr 2; unfold ceaseHeat heated; apply Finset.sum_congr rfl; intro k _; exact congr_fun ( heat_m true (priceHx Φ P p h i hs) _ j hj ) z
variable {u v: StockT P p i.prev}
lemma buy (hv:Matches r u v)(m:ℕ): Matches r (riseM Φ K P L p i m x u) (riseM Φ K P L' p i m y v):=by
    have hh:Matches r (Arm.columns (U_ i) (Recv P p i u)) (Arm.columns (U_ i) (Recv P p i v)):= by intro j hj; unfold Arm.columns Cluster.present; rw [lettering P p i hv j hj]
    let L₁:=Arm.spins (U_ i) (F_ i) (K_ i); intro j hj;ext1 z; unfold See.riseM Arm.OutputM collectO; apply congr_arg (Packet.crop _); apply congr_arg; unfold endHeat heated; apply Finset.sum_congr rfl; intro k _; exact congr_fun ( mark_m (L:=L₁) hh ( heat_m true (priceHx Φ P p h i hs) ) _ j hj ) z
end Film
lemma owned : ∀ i, Matches r ((See.work Φ K P L p) i) ((See.work Φ K P L' p) i):=by
 apply Page.proves
 · intro x; exact topV h x _ -- G explicit?
 intro w hh; rw [itinerary,itinerary]; exact predict Φ K P p h w hh
lemma aligns : ∀ i,A i.bindW= A' i.bindW→ Matches r ((See.observe Φ K P A L p) i) ((See.observe Φ K P A' L' p) i):= by
 apply Page.proves
 · intro x hx; change A x=A' x at hx; change Matches r (Boot.view (A x) _) (Boot.view (A' x) _); rw [hx]; exact fun _ _=>rfl
 intro i H hp; rw [See.display,See.display]; exact buy Φ K P p h i ( owned Φ K P p h _ ) ( H hp ) m
-- positional report. h∃Φ.Height e & Clean.Horonized stationary.L.K β through p. Age-bit.
variable {I:Type}[DecidableEq I][Fintype I]
variable (H: Marker.Census I)(u:I) (s:ℕ)(W: See.Times L s)(F:See.Agenda P H p)(t:ℕ)(V: See.Times L' t)(J:See.Agenda P H p)
include Y Φ
open Exterior
lemma visibleMark (x:Page M)(w: fieldDir G (f_ x) 1)(hx:r ≤ s)(ht:r ≤ t)(hS:∀ i:X, L (Page.opening M i)= Clocks.flat)(hT:∀ i:X,L' (Page.opening M i)= Clocks.flat)(hf:A x.bindW=A' x.bindW)(hk:Setup K P H u A L p s W F)(he:Setup K P H u A' L' p t V J) : prime P H u L p s W F (x:=x) w r= prime P H u L' p t V J (x:=x) w r:=by
 rw [(observes Y Φ K P H u A L p s W hS hk _ _ hx).1,(observes Y Φ K P H u A' L' p t V hT he _ _ ht).1]; unfold Uniforms.cuff; rw [ flavor_lo, flavor_lo, aligns Φ K P p h _ hf r le_rfl ]
end YM.RegulatorIR.FVAAlt2.Pipeline.Hours
