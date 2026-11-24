import YM.RegulatorIR.Sources.Currency

/-!
# RegulatorBudget release for assessed stencils and real profiles

Only before older stop phase choice. Stronger Sect scale choices projected
from the bulk cover bounds. Needs supplies of one-mark algebra seminorms,
no multiproduct. Keep translation & count & even & epoch hypotheses visible.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Sources
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Centered Labels Source Aperture Address.Calendar Collapsed
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I X Y A B: Type}{q u b p a i j e k d m r:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{D:Choice M}
variable {S:Heir n G} (R:Reel S)(T:S.Accounts)
variable {U': Flap M→ Layer (Foot G) (Foot G)}{V': Flap M→Bride G}
variable {γ:ℝ}{c:Flap M→ℝ≥0∞}

section Source
variable {F:Labels.Frame G d}{H:Hol G}(Z:Fabric R F H)(Φ: W→ PhaseTests d)

def phaseD (Z: W→ Set Room)(u:plane W): Set Room:= {t | t-u.2∈Z u.1}
def exposed (Q: W→PhaseTests d)(m:ℕ)(h:∀ w,ContDiff ℝ m (Q w).phi) (l: plane W→ℝ)(u:plane W) := codeS (l u) u.2 _ (h u.1)
structure Visible (Z:W→ PhaseTests d)(V: W→Set Room)(m:ℕ)(L:Meter W):Prop where
 ink : ∀ w,ContDiff ℝ m (Z w).phi
 lived : ∀ w,(V w).Nonempty
 spread : ∀ w,IsClosed (V w)
 lands : ∀ w,tsupport (Z w).phi⊆ V w
 bank : ∀ w, V w ⊆ Metric.closedBall 0 (Z w).radius
 width : Poly L fun w=> ENNReal.ofReal (Z w).radius
 -- derivatives in moving units up to m (which can exceed the input weight, supplied in RG08 S3)
 cash : ∃ c,Poly L c ∧ ∀ w (p:Category m) x, ‖feeD (Z w).phi p x‖ₑ≤ c w

def Mature (D:Choice M): Page D.before.spans→Page M:=D.before.page
structure S3 (D:Choice M)(L:Meter W)(p m k:ℕ)(σ:ℝ):Prop where
 -- cov moment-kme theorem on operative algorithm. choose representatives through all requested e only, no compact tests in constants.
 pays : ∃ K:∀ _l:Page D.before.spans, (i j:ℕ)→ TagList (Foot G) (Token m) j, (∀ l,∀ i≤p,∀ j,Bondage R T Z (K l i j) (Mature D l) i) ∧ ∀ i≤p,∀ j,Carry (coverL D.before.spans L) (fun l=> ENNReal.ofReal ((S.ε l.bindW/S.l (Mature D l))^σ)) fun l=> (meterC (S:=S) (Mature D l)).kme (K l i j) k
variable {V: W→ Set Room}
variable (P:Passage R)(N: Lantern S D L c γ)(G₀: SchemeBeam R T U' V' L c p k) (I₀:Visible Φ V m L){σ:ℝ} (Yζ:S3 R T Z D L p m (tileC u a) σ)
include I₀ N G₀
omit G₀ I₀ in
private lemma levelsP : ∀ w:Page D.before.spans,0 < S.l (D.before.page w) ∧ S.l (D.before.page w) ≤1:=by
 let E:=D.before.expanse S;intro w
 have h:= E.tails w
 change S.l _≤ S.l (D.before.page (D.lastPage w.bindW)) at h; rw [D.meet,N.ref_mesh] at h; exact ⟨S.hl _,h⟩
include P Yζ
lemma wards : tasks (p:=p) (spool D (film W)) (motif S) (L.us (film W)) (fun w=> (fresco R T Z Φ).main ((spool D (film W)).before.page w)) u a (phaseD V) σ d:=by
 obtain ⟨t,h,H⟩:= Yζ.pays; obtain ⟨c,hc,hv⟩:= I₀.cash
 let F:= film W; let D':=spool D F; let K:= (motif S); let E:=dawn D' (motif S); let L':= L.us F
 let P':= Page D'.before.spans; let U:P'→ Page D.before.spans:= stages F D.before.spans
 let g (w:P'):= Mature D (U w)
 let costB:P'→ℝ≥0∞:= fun w=> c w.bindW.1; let h':=fun w:plane W=> (Φ w.1).radius
 have hu (w:P'):E.l w =S.l (g w):=rfl; have hz(w:P'): E.l w≤1:= (levelsP N (U w)).2 -- args?
 let X(w:P'):= meterC (S:=S) (g w);let Z':=fun w:P'=> Φ w.bindW.1; let Bd(w:P'):= codeS (E.l w) w.bindW.2 (Z' w).phi (I₀.ink w.bindW.1)
 have hp (w:P') : (X w).home= Stations E w:=by change _=(S.maps (g w)).pos;rw [R.realms];rfl
 let Tu(w:P'):= t (U w); let s (w:plane W):=w.2
 have he (w:P') : Bills (Bd w) (phaseD V w.bindW) (s w.bindW) (h' w.bindW) (costB w):= by exact parish (Z' w) w.bindW.2 (V w.bindW.1) (I₀.lands w.bindW.1) (I₀.bank w.bindW.1) _ (E.hl w) (hz w) (hv w.bindW.1)
 have hh i (hl:i≤p) j : Carry (coverL D'.before.spans L') (fun l=> ENNReal.ofReal ((E.ε l.bindW/E.l l)^σ)) fun l=> (X l).kme (Tu l i j) (tileC u a):= (H i hl j).us U
 intro i hi j; convert restoration (A:=X) (L:=L') (h:=d) E Bd hz hp he (hc.us (F ∘ Page.bindW)) (I₀.width.us F) (fun w=> (Φ w.1).priceR) hh i hi j using 1;ext1 w; exact localRestore R T Z Φ (Tu w i j) (g w) (h (U w) i hi j) (w.bindW.2) P G₀.rates.run G₀.port G₀.milieu hi
end Source

section Array
variable (T:S.Accounts) {m d: I→ℕ}
variable {F:∀ i,Labels.Frame G (d i)}{H:Hol G}
variable (Z: (i:I)→ Fabric R (F i) H) (Φ: (i:I)→ W → PhaseTests (d i))
variable {V: I→W→Set Room}{d':W→ℝ}{σ:I→ℝ}

structure Envelope (Φ:(i:I)→W→PhaseTests (d i))(V:I→W→Set Room)(d':W→ℝ)(L:Meter W)(m:I→ℕ)(J:Composite I): Prop where
 leads : ∀ i,J.In i → Visible (Φ i) (V i) (m i) L
 positive : ∀ w, 0<d' w
 rating : Poly L fun w=> ENNReal.ofReal ((d' w)⁻¹)
 separate : ∀ w,J.Distinct (fun i=>V i w) (d' w)
variable (J:Composite I) (K:Envelope Φ V d' L m J)
private def huge_ (J:Composite I)(Φ:(i:I)→W→PhaseTests (d i))(w:W) :ℝ:=match J with
 | .atom i=>(Φ i w).radius
 | .pair a b=>huge_ a Φ w + huge_ b Φ w
private lemma capacitate (J:Composite I) (Φ:(i:I)→W→PhaseTests (d i))(h:∀ i,J.In i→ Poly L fun w=> ENNReal.ofReal (Φ i w).radius): Poly L (fun w=> ENNReal.ofReal (huge_ J Φ w)) ∧ (∀ w,0≤ huge_ J Φ w) ∧ ∀ i,J.In i→∀ w,(Φ i w).radius ≤ huge_ J Φ w :=by induction J with
 | atom i=> exact ⟨h i rfl,fun w=>(Φ i w).priceR,fun j hz w=> by rw [show j=i from hz]; exact le_rfl⟩
 | pair a b ih ih'=>
    have ht:= ih fun i h'=>h i (Or.inl h'); have hx:=ih' fun i h'=>h i (Or.inr h')
    refine ⟨(ht.1.add hx.1).mono (fun w=>?_),fun w=> add_nonneg (ht.2.1 w) (hx.2.1 w),?_⟩
    · exact ENNReal.ofReal_add_le ..
    rintro i (hi|hi) w
    · exact (ht.2.2 i hi w).trans (le_add_of_nonneg_right (hx.2.1 w))
    exact (hx.2.2 i hi w).trans (le_add_of_nonneg_left (ht.2.1 w))
private lemma apartV (J:Composite I)(V:I→W→Set Room)(w:plane W)(g:ℝ)(h:J.Distinct (fun i=>V i w.fst) g): J.Distinct (fun i=>phaseD (V i) w) g:=by induction J with
 | atom i=>trivial
 | pair P Q ih ih'=>
    refine ⟨ih h.1,ih' h.2.1,fun i hi j hj y hy x hx=>?_⟩; apply le_trans (h.2.2 i hi j hj (y-w.2) hy (x-w.2) hx); simp
include K
lemma glare : Typical (dwell W) (fun i=> phaseD (V i)) (d' ∘ film W) J (L.us (film W)):=by
 obtain ⟨c,hc,H⟩:=capacitate J Φ (fun i hi=>(K.leads i hi).width); refine ⟨?_,?_,?_,fun w=>K.positive w.1,⟨_,c.us (film W), fun w=>⟨hc w.1,?_⟩⟩,K.rating.us (film W)⟩
 · intro i hi w; obtain ⟨x,hx⟩:= (K.leads i hi).lived w.1; exact ⟨w.2+x,by change w.2+x-w.2∈ V i w.1; rwa [add_sub_cancel_left ..]⟩
 · intro i hi w; exact ((K.leads i hi).spread w.1).preimage (continuous_id.sub (continuous_const (y:=w.2)))
 · intro w; exact apartV J V w _ (K.separate w.1)
 intro y hy; obtain ⟨i,hi,hx⟩:= (J.covers ..).mp hy; refine le_trans ?_ (H i hi w.1); have hv:= (K.leads i hi).bank w.1 hx; change dist (y-w.2) (0:Room)≤ _ at hv;exact (by simpa [dwell,dist_eq_norm] using hv)

variable (P:Passage R)(N: Lantern S D L c γ)(G₀: SchemeBeam R T U' V' L c p k) (Yζ:∀ i,J.In i → S3 R T (Z i) D L p (m i) (tileC (plusU b u) a) (σ i)) (hm:0≤J.loss σ)
include G₀ P N Yζ hm

def CorpsUp (Z:(i:I)→ Fabric R (F i) H)(Φ:(i:I)→W→ PhaseTests (d i)) (t:I) := frown R (Z t) (Φ t)
abbrev Stall (T:S.Accounts) (t:I) := fresco R T (Z t) (Φ t)

lemma chants : Rosters (CorpsUp R Z Φ) (Stall R Z Φ T) (spool D (film W)) p (plusU b u) a σ d d (fun i=> phaseD (V i)) (L.us (film W)) J:= ⟨fun i _ w=>spoken R T (Z i) (Φ i) w,fun i hi=> wards R T (Z i) (Φ i) P N G₀ (K.leads i hi) (Yζ i hi),hm⟩
end Array
end YM.RegulatorIR.Sources
