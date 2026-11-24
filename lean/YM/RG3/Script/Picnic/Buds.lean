import YM.RG3.Script.Picnic.Bower
/-! # Bringing projection purchases over joint families. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition RG3.Primary Push.Local Source
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V : Type} [DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge}
  {X:Type*}{P:Rep G n} {d:X→Deck R P}{T:X→Edition ζ R G}
  {D:V→ℕ} (H:Hol G) {I:(s:V)→ Labels.Frame G (D s)}(L:(s:V)→SectionData (I s))
variable {a u v Y δ:ℝ}{k w:V→ℝ}
  (hr:∀ i,Readable H (L i) P.p n (k i))

namespace Firm
variable (h:Firm T)
include h
lemma seat x y i : (T x).shaft i=(T y).shaft i:=by
  cases hx:(T x).shaft i with
  | none=> cases hh:(T y).shaft i with
    | none=> rfl
    | some s=> exfalso; apply (T x).nobody hx s; unfold only; rw [h.pins x y]; exact (T y).from_shaft hh
  | some s=> have hf:= (T x).from_shaft hx; unfold only at hf; rw [h.pins x y] at hf; exact ((T y).shaft_only hf).symm
lemma sky (d : X→ Deck R P) x y i : (T x).tent L (d x) i=(T y).tent L (d y) i := by
  let F (x : X) := fun u : V=> if (T x).pins i=R.fire u then joint (L u) (ζ u) ((T x).home i) else (T x).home i; change ((T x).shaft i).elim ((T x).home i) (F x) = ((T y).shaft i).elim ((T y).home i) (F y); unfold F
  rw [h.home x y,h.pins x y,h.seat x y]
lemma paddle (d : X→Deck R P) (k:V→ℝ) (f m:ℕ→ℝ) (I:(s:V)→Labels.Frame G (D s)) x y : Edition.palm (T x) (d x) H k m f I=Edition.palm (T y) (d y) H k m f I:=by
  funext i; unfold Edition.palm Primary.ink Primary.earns Edition.scribe; dsimp only; rw [h.pins x y,h.seat x y]
include hr
lemma scattering (d : X→Deck R P): Ledger (fun x=> Edition.tonic (d x) (T x) H L hr) := by
  constructor; intro x y i; unfold tonic jointFeed feeds Primary.stem Edition.scribe; dsimp only; refine Prod.ext (Subtype.ext ?_) rfl; simp only; rw [h.home x y]

omit hr
variable [Fintype V]
lemma spray (d : X→Deck R P): Firm (fun x=> (T x).sprayed H L (d x)):= by
  constructor
  · intro i j; unfold Edition.sprayed; dsimp only; rw [funext (sky L h d i j)]
  · intro i j; unfold Edition.sprayed; dsimp only; rw [h.pins i j]
  exacts [h.tag,h.cover]
end Firm

variable [Fintype V][Nonempty V]
  (hz: ∀ i,(d i).contents.origins=ζ) (hd:∀ i,(d i).Active) {f m g:ℕ→ℝ}
  (hc: Voucher T P.p w a u v Y f g) (h: ∀ x, Loaded H a m δ L (d x) (T x) k w)(hw:∀i,0<w i)(ha:P.p.supportExponent+1 ≤ a)
  {K : ℝ}(hK : ∀ i, expense P.p.B a ((L i).footprint (ζ i)) (k i) ≤ K)
include hz hd hc h hw ha hK hr
omit [Nonempty V] in
lemma summer (b:X):
    Voucher (fun x=> (T x).sprayed H L (d x)) P.p w a (u+δ) ((v+δ)+K*δ) Y (shuffle (stageCost k w δ) (palm (T b) (d b) H k m f I)) g:= by
  refine ⟨hc.toFirm.spray H L d, fun x=> primed H (d:=d x) hr (hz x) (hd x) (hc.stays x),fun x=>?_,hc.fiscal,fun x=>hc.ticket x⟩
  rw [hc.toFirm.paddle H d k f m I b x]
  exact stored (d:=d x) hr (hz x) (hd x) (hc.stays x) (h x) hw (hc.backs x) ha hK
end YM.RG3.Script.Picnic
