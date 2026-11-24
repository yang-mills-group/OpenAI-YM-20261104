import YM.RegulatorIR.Ledger.Milky

/-! Space comparisons extended to radius max(1,λ) after the history-independent
charges. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type} (S:Sky X Y) (T:S.Accounts)
variable {u b p:ℕ}{L: Meter W}

def radius (w) := max 1 (S.l w)
lemma radius_pos (w) :0 < S.radius w:= lt_of_lt_of_le (S.hl _) (le_max_right ..)
lemma radius_climb (w: Flap M):S.radius w.prev ≤ S.radius w.next:= max_le_max_left _ (S.climb _)
def ridge (w:Flap M):=S.radius w.next
lemma ridge_pos (w):0<S.ridge w:=S.radius_pos w.next
lemma ridge_more (w):S.ceiling w ≤ S.ridge w:=le_max_right ..

def maximal (S:Sky X Y) := S.census.lease S.radius S.radius_pos
def placement := S.lifts.incoming S.ridge S.ridge_pos
def camp := S.lifts.incoming (S.radius ∘ Flap.prev) (fun _=>S.radius_pos _)

def step_center (M:W→ℕ) (x: W→Room) (w: Flap M):Room:= x w.volW
def stage (M:W→ℕ) (x:W→Room) (w:Page M): Room:= x w.bindW

def yard (x:W→Room)(u:ℕ) w := S.placement.rooted (step_center M x) u w
def Plaza (x:W→Room)(u:ℕ) w:= S.placement.anchored (step_center M x) u w
def coverQ (x:W→Room) (u:ℕ) w:= S.maximal.rooted (stage M x) u w
def markUp (x:W→Room) (u:ℕ) w:= S.maximal.anchored (stage M x) u w

private lemma raise_p {Z:Type} {A B:W→Tariff Z} {X Y:W→Type} {x:∀ w,X w→Z}{y:∀ w,Y w→ Z}{Γ:∀ w,Curve (X w) (Y w)} {i:ℕ}(h: SmoothPrice L A x y Γ i)(H:∀ w x y,(B w).road x y≤(A w).road x y): SmoothPrice L B x y Γ i:= by
 obtain ⟨f,hf,Hf⟩:= h; refine ⟨f,hf,fun w a=>le_trans ?_ (Hf w a)⟩
 exact quota_mono _ fun _=> Premium.prem_mono (B:=(Premium.rooted (B w) (x w a)).uses (y w)) (D:=(Premium.rooted (A w) (x w a)).uses (y w)) (fun _ _ => H w _ _) (fun _=> H w _ _) _
private lemma fewer (w:Flap M) {d:ℝ} (hv:0≤d): amount (S.ridge w) u d ≤ amount (S.ceiling w) u d:=by have h₁:= S.ridge_more w; have h₂:= S.high w; unfold amount; gcongr
lemma adv (G:S.Primitive L p b)(he:u ≤ b)(i:ℕ)(hx:i ≤ p) : SmoothPrice (flapL M L) (fun w=> native _ (S.ridge_pos w) u) (fun w=> (S.lifts.fine w).pos) (fun w=>(S.lifts.coarse w).pos) (fun w=>(S.sight w).space) i := raise_p (G.prices u he i hx) (fun _ _ _=> S.fewer _ dist_nonneg)
lemma adv_pair (G:S.Primitive L p b)(he:u ≤ b) (i:ℕ)(hx:i ≤ p): SmoothPrice (flapL M L) (fun w=> onFold _ (S.lifts.positive w) _ (S.ridge_pos w) u) (fun w=> (S.lifts.fine w).atO) (fun w=>(S.lifts.coarse w).atO) (fun w=>(S.sight w).run) i:= raise_p (G.charges u he i hx) (fun _ _ _=> S.fewer _ (distance_nonneg ..))
lemma get_drift (G:S.Primitive L p b)(he:u ≤ b): Beam (flapL M L) ((S.lifts.insideRoom S.ridge S.ridge_pos).cone u) S.lifts.forecast:= Post.beam_fewer (M:=S.ceilingRoom) (l:=S.ridge) S.ridge_pos S.ridge_more (S.ceilingRoom.descent G.drift he)
lemma pole_cost {c: Flap M→ℝ≥0∞}(H:S.Lead b c)(he:u ≤ b)(w:Flap M): Layer.row (swap (S.sight w).pole) ((S.lifts.insideRoom S.ridge S.ridge_pos).cone u w) id id (c w):=Layer.row_mono (fun _ _=> (S.fewer w dist_nonneg).trans (Tariff.moment_mono (S.high w) he dist_nonneg)) (H.down w)
end YM.RegulatorIR.Ledger.Sky
