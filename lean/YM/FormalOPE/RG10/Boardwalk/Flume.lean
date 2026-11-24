import YM.FormalOPE.RG10.Boardwalk.Fanfare
/-! # Scheme compared with the independent WilsonX top prescription

Retain coupling re-expression in local *moving* variable when comparing real arrays. The Plan
supplies its bare stencils every-construction and diagnostics; G generator still needs WilsonX
 alignment in the proofs of Fanfare and all orientation/support credentials. This file states the
 precise interface. The coupling change $f_{X,k}$ in that application will be the Peal diagnostic
 evaluated on full moving-mesh A-arrays. This section just proves they earn the announced values
 (close to WilsonX's bare arrays conformed and reoriented at one length) if needed precomparisons
 are proved. Includes calling on same branch for many heights. No choosing slope normalization
 from ad-hoc finite matching. Regulator t→ chosen before call.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Flume
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle Lawn
open RG10.Profile Gliss Gazebo Matrix Position.Grade Peal Trellis Fanfare
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge}{F:Frames G}{I:Type*}{l:Filter I}{P:Path l}{r d n:ℕ}
variable {Γ:Plan F}
local notation "κ" d=> Deck F d
local notation "K" d=> Matrix (Deck F d) (Deck F d) fps
local notation "Ψ" d=>Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "Δ"=>Γ.stock
local notation "ins" d=>PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n
variable {x:I→ Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
variable {f:I→Mark (Deck F 6) PertExtension.Physical.Profile.n→fps}
variable {V:I→ Matrix (Deck F d) (Deck F d) fps}{L:I→ Matrix (Deck F 6) (Deck F 6) fps}
variable {q:I→ℕ+}{m:I→ℕ}{p:I→Warp}
def translated (Γ:Plan F)(j:ℕ)(q:I→ℕ+)(m:I→ℕ)(p:I→Warp)(i:I) := (p i).charge ∘ Γ.begins (q i) (m i) j
local notation "τ" k => translated Γ k q m p
local notation "u" => τ d
local notation "v" => τ 6
variable (B:Fanfare P Γ.stock r (translated Γ d q m p) x V)(C:Fanfare P Γ.stock r (translated Γ 6 q m p) f L)
local notation "B'" k => fun (i:I) => Γ.begins (q i) (m i) k
-- orientation k.FK.Err.P. Need user-supplied Fk$(Fk-hyp). Force same q,m across heights.
omit B C in
lemma through (B:Plan F){q:ℕ+} (p:I→Warp)(hq:1<q.val)(h:Tendsto m l atTop): listens (D:=B.stock) (l:=l) (translated B d (fun _=>q) m p):= by
 apply tendsto_pi_nhds.mpr; intro i; change Tendsto (fun a=>constantCoeff _) _ _; unfold translated; simp_rw [Function.comp_apply,Warp.smoothed]; exact (Plan.starts hq B (markIn (B.stock d).tests i)).comp h

include B
lemma prepared : ∀ᶠ i in l, Credible Δ (Γ.begins (q i) (m i) d):= by
 apply credential B.standard (B' d); apply B.heartbeat.congr'
 filter_upwards with i; unfold Carryon.probe; funext j; exact Warp.smoothed ..

lemma standardizes : ∀ᶠ i in l, post Δ (u i)=(p i).charge ∘ (Γ.dressed (q i) (m i) d):= by
 filter_upwards [prepared B] with i hi; exact Warp.publish (p i) B.standard hi
omit B
include C
lemma together : ∀ᶠ i in l, (fun x=> peal Δ (translated Γ 6 q m p x)) i=(p i).step (Carryon.charged (Γ.dressed (q i) (m i) 6)) := by -- C notation
 filter_upwards [standardizes C] with i hi; unfold peal; rw [hi]; exact Warp.trade ..
-- forward change computed in g_k. earns stability coefficient comparison with top & its X converter; then effect after recalculation at X variable
lemma expenses (hk:Polls P r v f L) : Posi P r (fun i=>(p i).charge (Plan.coin F Γ (q i) (m i))) (fun i=> (peal Δ (f i)).x):= (C.fares hk).fits ((together C).mono fun _ hi=> congr_arg Warp.x hi) Filter.EventuallyEq.rfl

variable (R:Position.Grade.Rails F) {a:ℝ}(h:a≠0)(he: Tendsto (fun i=> coeff 1 (peal Γ.stock (translated Γ 6 q m p i)).x) l (𝓝 a))
include B h he
lemma lift : ∀ᶠ i in l,R.coarse (P:=Γ) (q i) (m i) d=rear Δ R (v i) (u i):= by
 filter_upwards [standardizes C,standardizes B,together C,he.eventually (isOpen_compl_singleton.mem_nhds (s:=({0}ᶜ:Set ℝ)) h)] with i hp ht hm hi
 let M:= Γ.dressed (q i) (m i) 6; let q' := peal Δ (v i)
 let k:= p i
 have hq' : q'.Hot:= hi
 have h':= (Carryon.Warp.flames k (charged M)).mp (hm ▸ hq' : (k.step (charged M)).Hot)
 unfold Position.Grade.Rails.coarse rear peal; rw [hp,ht]; apply congr_arg (fun g=>PertExtension.Position.insert (Deck F d) _ g _); funext j
 exact (Carryon.Warp.trading k M h'.2 h'.1 _).symm

-- only on one given probe family. NOTρ-growing absent Polls and Faces for those cores.
variable {x₀:I→Test n}(hx: Polls P r (translated Γ 6 q m p) f L)(hy: Faces P r (translated Γ d q m p) x V x₀)
include hx hy
lemma walks : Stage P r (fun i=> R.coarse (P:=Γ) (q i) (m i) d) (fun i=> rear Δ R (f i) (x i)) x₀:= (B.measured C hx R h he hy).fit ((lift B C R h he).mono fun _ hp=> hp.symm) Filter.EventuallyEq.rfl

-- equality after charging both back in A's coupling warp (Peal computed on A-vectors). Identical for A side.
lemma applied (hu:1≤r) : Stage P r (fun i=> (peal Δ (f i)).charge ∘ R.coarse (P:=Γ) (q i) (m i) d) (fun i=> adjusted Δ R (f i) (x i)) x₀:= by
 let p':= fun i=>peal Δ (f i)
 have hm:= (walks B C R h he hx hy).calendar (p:=p') (q:=p') (Posi.same (C.fares hx).rights)
 apply hm.fit Filter.EventuallyEq.rfl
 have ht : Tendsto (fun i=> coeff 1 (p' i).x) l (𝓝 a):= (C.fares hx 1 hu).both _ he
 filter_upwards [ht.eventually (isOpen_compl_singleton.mem_nhds (s:=({0}ᶜ:Set ℝ)) h)] with i hi; exact (Fanfare.priced R Δ _ (f i) hi).symm -- order of arguments
end YM.FormalOPE.RG10.Boardwalk.Flume
