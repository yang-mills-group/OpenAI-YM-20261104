import YM.RegulatorIR.Centered.Demand

/-! Use a family of inputs varying with center and geometry, but with matching
scales, vacuum history, and terminal unsoftening data at each tested center.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Centered
open Topology Lattice MeasureTheory Set Metric Function Motion Spatial
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Ledger Ledger.Sky Step Diagram Gradient
open scoped ENNReal NNReal BigOperators Classical
variable {W Z : Type} {M:W→ℕ}{X Y:Page M→Type}

def stages (f:Z→W)(M:W→ℕ)(i:Page (M ∘ f)):Page M:=⟨f i.bindW,i.downW,i.good⟩
def arrow (f: Z→ W)(M:W→ℕ)(i:Flap (M ∘ f)):Flap M:=⟨f i.volW,i.offset,i.ok⟩
def album (S:Sky X Y)(f: Z→W): Sky (fun w:Page (M ∘ f)=> X (stages f M w)) (fun w=> Y (stages f M w)) where
 P := S.P ∘ f
 hp w:= S.hp (f w)
 l w:= S.l (stages f M w)
 hl w:= S.hl (stages f M w)
 climb w:= S.climb (arrow f M w)
 maps w:= S.maps (stages f M w)
 frames w := S.frames (arrow f M w)
 sight w:= S.sight (arrow f M w)

variable {S:Sky X Y} {L:Meter W}
def movie (T: S.Accounts)(f: Z→ W): (album S f).Accounts where
 bulk w:= T.bulk (stages f M w)
 orb w:= T.orb (stages f M w)
 step_v w:= T.step_v (arrow f M w)
 step_o w:= T.step_o (arrow f M w)
 top_v w:= T.top_v (f w)
 top_o w:= T.top_o (f w)
variable {T:S.Accounts}{m:ℕ}
def series (R:T.Report m)(f:Z→W) : (movie T f).Report m where
 main w:= R.main (stages f M w)
 point w:= R.point (stages f M w)
 step_m w:= R.step_m (arrow f M w)
 step_p w:= R.step_p (arrow f M w)
 ceilingM w:= R.ceilingM (f w)
 ceilingP w:=R.ceilingP (f w)
 same w:=R.same (f w)

def spool (k:Choice M)(f:Z→W): Choice (M ∘ f):=⟨k.age ∘ f,fun i=>k.young (f i)⟩
def post (F:Margins Y)(f:Z→W): Margins (fun w:Page (M ∘ f)=> Y (stages f M w)):=⟨fun w=> F.endK (f w),fun w=>F.haar (f w)⟩

variable {k j : Ledger.Choice M}{γ:ℝ}{p b h q α u:ℕ}{c: Flap M→ℝ≥0∞}{x: W → Room}
private lemma price_re {Q W Z : Type} {X Y : W→Type} {A:W→Tariff Q}{x:∀ w,X w→Q}{y:∀ w,Y w→ Q}{Γ:∀ w, Curve (X w) (Y w)} {L:Meter W} (h:SmoothPrice L A x y Γ p)(f:Z→W): SmoothPrice (L.us f) (fun w=>A (f w)) (fun w=>x (f w)) (fun w=>y (f w)) (fun w=>Γ (f w)) p:= by obtain ⟨c,hc,H⟩:=h; exact ⟨_,hc.us f,fun w=>H (f w)⟩
lemma primitive (f:Z→W)(B:S.Primitive L p b): (album S f).Primitive (L.us f) p b where
  depth := B.depth.us f
  line := B.line.us (arrow f M)
  add_cost i h j:= (B.add_cost i h j).us (arrow f M)
  drift:= B.drift.us (arrow f M)
  deckLine w:= B.deckLine (arrow f M w)
  deckAdd w:=B.deckAdd (arrow f M w)
  deckDrift w:=B.deckDrift (arrow f M w)
  ground w:=B.ground (arrow f M w)
  grade w:= B.grade (arrow f M w)
  prices b hb i hi:= price_re (B.prices b hb i hi) (arrow f M)
  charges b hb i hi:= price_re (B.charges b hb i hi) (arrow f M)
lemma galaxy (f:Z→ W)(B:S.Cosmos T u b p L): (album S f).Cosmos (movie T f) u b p (L.us f):= by
 refine { prim:=primitive f B.prim, space:=?_, tops:=fun w=>B.tops (f w), ward:=fun w=> B.ward (arrow f M w), counted:=B.counted.us (arrow f M) }
 exact ⟨fun i hi j=> (B.space.bulk_price i hi j).us (stages f M),fun w => B.space.bulk_deck (stages f M w)⟩
lemma glow (f:Z→W)(R:S.Radiants L γ u α c k): (album S f).Radiants (L.us f) γ u α (fun w=> c (arrow f M w)) (spool k f) where
 ref_mesh w:= R.ref_mesh (f w)
 gleams:= R.gleams
 small:=R.small
 scale:= R.scale.us (arrow f M)
 lead:= ⟨fun w=> R.lead.down (arrow f M w),fun w=> R.lead.cap (arrow f M w)⟩
 cold w:= R.cold (arrow f M w)
 side w:= R.side (f w)
lemma models (f:Z→ W){t:W→ℝ≥0∞}(R:T.Report m)(H:S.Preserved T R t h p k x u L): (album S f).Preserved (movie T f) (series R f) (t ∘ f) h p (spool k f) (x ∘ f) u (L.us f):= fun i hv j=> Claim.us (H i hv j) (stages f k.before.spans)
lemma zest (f: Z→ W) (F:Margins Y) (h:S.Epoch F L u p): (album S f).Epoch (post F f) (L.us f) u p:= ⟨h.vane.us f,fun i hi j=> (h.sphere i hi j).us f,fun w=>h.positive (f w)⟩
end YM.RegulatorIR.Centered
