import YM.RegulatorIR.Ledger.Scalar

/-! Cutting intervals at measuring scale and at older report scale. Bounds
are charged to a single geometry polynomial. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger
open Budget Spatial Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient ENNReal Sky
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W: Type} {M:W→ℕ} {X Y:Page M→Type}

structure Era (M : W→ℕ) where
 age : W→ℕ
 spans : W → ℕ
 duration : ∀ w, age w+ spans w ≤ M w

namespace Era
variable (E : Era M)
def page (i:Page E.spans): Page M:=⟨i.bindW,E.age i.bindW+i.downW,(Nat.add_le_add_left i.good (E.age i.bindW)).trans (E.duration i.bindW)⟩
-- force definitionally equal sums
def wing (i:Flap E.spans): Flap M:= ⟨i.volW,E.age i.volW+i.offset,lt_of_lt_of_le (Nat.add_lt_add_left i.ok _) (E.duration _)⟩

variable (S:Sky X Y)
def expanse : Sky (fun w=> X (E.page w)) (fun w=> Y (E.page w)) where
 P:= S.P
 hp:= S.hp
 l := S.l ∘ E.page
 hl _:= S.hl _
 climb w := S.climb (E.wing w)
 maps w:= S.maps (E.page w)
 frames w:= S.frames (E.wing w)
 sight w:= S.sight (E.wing w)

variable {p b e r u:ℕ}{c:Flap M→ℝ≥0∞}{L:Meter W}
private lemma price_re {Z W W' : Type} {X Y : W→Type} {A:W→Tariff Z}{x:∀ w,X w → Z}{y:∀ w,Y w→ Z}{Γ:∀ w, Curve (X w) (Y w)} {L:Meter W} (h:SmoothPrice L A x y Γ e) (f:W'→W): SmoothPrice (L.us f) (fun w=>A (f w)) (fun w=> x (f w)) (fun w=>y (f w)) (fun w=>Γ (f w)) e:= by obtain ⟨c,hc,H⟩:=h; exact ⟨_,hc.us f,fun w i=>H _ i⟩
lemma sector (B:S.Primitive L p b):(E.expanse S).Primitive L p b where
  depth:= B.depth.mono fun w=>by change (↑(E.spans w):ℝ≥0∞) ≤ ↑(M w); exact Nat.cast_le.mpr (by have h:= E.duration w; omega)
  line := B.line.us E.wing
  add_cost i hi j:= (B.add_cost i hi j).us E.wing
  drift:= B.drift.us E.wing
  deckLine w:= B.deckLine (E.wing w)
  deckAdd w i j he:= B.deckAdd (E.wing w) i j he
  deckDrift w:= B.deckDrift (E.wing w)
  ground w:= B.ground (E.wing w)
  grade w:= B.grade (E.wing w)
  prices b h i hi:= price_re (B.prices b h i hi) E.wing
  charges b h i hi:= price_re (B.charges b h i hi) E.wing

lemma restrict (H:S.Lead b c): (E.expanse S).Lead b (c ∘ E.wing):=⟨fun w=> H.down (E.wing w), fun w=> H.cap (E.wing w)⟩

variable {T:S.Accounts}
def part (T:S.Accounts)(B:S.Primitive L p b): Sky.Accounts (E.expanse S) where
 bulk:= fun w=> T.bulk (E.page w)
 orb:=fun w=> T.orb (E.page w)
 step_v w:= T.step_v (E.wing w)
 step_o w:= T.step_o (E.wing w)
 top_v _:= T.cap_b B.grade (E.page _)
 top_o _:= T.cap_o B.grade (E.page _)
lemma getN (N:S.Supplies T L p b)(B:S.Primitive L p b): (E.expanse S).Supplies (E.part S T B) L p b:=⟨fun i hi j=> (N.bulk_price i hi j).us E.page,fun w i j hi=> N.bulk_deck (E.page w) i j hi⟩
lemma credit {α:ℕ} {d:Page M→ℝ≥0∞}(H:S.Softness u L c d α): (E.expanse S).Softness u L (c ∘ E.wing) (d ∘ E.page) α:= ⟨E.restrict _ H.fund,fun _=>H.root _,fun _=>H.limit _,fun w=> H.cool (E.wing w), H.past.us E.wing,fun w=> H.warm (E.wing w)⟩
end Era

structure Choice (M: W→ℕ) where
  age : W→ℕ
  young : age≤M

namespace Choice
variable (j:Choice M)
def before: Era M:= ⟨fun _=>0,j.age,by simpa using! j.young⟩
def after: Era M:= ⟨j.age,fun i=> M i-j.age i,fun i=> by have h:j.age i ≤ M i:= j.young i;omega⟩
def choose (w:W): Page M:= ⟨w,j.age w,j.young w⟩
def firstPage (w:W): Page j.after.spans:= Page.opening _ w
def lastPage (w:W):Page j.before.spans:= Page.finallyW _ w
lemma meet (w:W): j.before.page (j.lastPage w)= j.choose w:=by unfold lastPage Page.finallyW Era.page choose; simp [Choice.before]
lemma finalPage (w:W): j.after.page (Page.finallyW _ w)= Page.finallyW _ w:=by unfold Page.finallyW Era.page; simp [Choice.after,Nat.add_sub_of_le (j.young w)]
end Choice

namespace Sky
variable (S:Sky X Y)
lemma heads (w:Page M): S.l (Page.opening M w.bindW) ≤ S.l w:= by
 apply Page.proves (g:=fun w=> S.l (Page.opening M w.bindW)≤ S.l w) (fun _=>le_rfl) (fun f hf=> hf.trans (S.climb f)) w
lemma tails (w:Page M):S.l w≤ S.l (Page.finallyW M w.bindW):=by
 rcases w with ⟨w,i,h⟩; let j : Choice M:=⟨Function.update M w i, fun u=> by by_cases hp:u=w <;> simp [hp,h]⟩
 have hh:= (j.after.expanse S).heads (Page.finallyW _ w)
 change S.l (j.choose w) ≤ S.l (j.after.page (Page.finallyW _ w)) at hh
 rw [j.finalPage, show j.choose w=⟨w,i,h⟩ by simp [j,Choice.choose, Function.update]] at hh; exact hh
end Sky
end YM.RegulatorIR.Ledger
