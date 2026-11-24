import YM.RG3.Script.Reserve
/-!
# Need the actually stronger buy on the whole K before Text merger.
License such merger if service has been registered with a stronger
quantitative program. This still recovers the literal chosen-profile
from Test, retaining also total hits at the stronger exponent for every
held field on the component (may instead register at each).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Reserve
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Law RG3.Ink
  Extra.Multi Extra.Trajectories Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration Edition Push.Local Source Estate Picnic
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V ι : Type*}[DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge} {w:V→ℝ}
  {P : Rep G n}
variable {t α c :ℝ}{d : Deck R P}{f : Feed G n R ι}(D : Forms.Test d f t w α c) (B : ℝ)

/-- New stronger Hit at SAME cents. Can regenerate the Test object with
B and re-certified ledger at the lowered exponent (adapter below). The
flow exported has same density and layout regardless, but need quantitative
bounds on the actual corresponding invoice to use those **profiles**. -/
structure Bar (u α c : ℝ): Prop where
  above : P.p.supportExponent ≤ B
  vac:Hit (fun i => (P.activities.forced i).support) P.p.B D.vac (B+1) α
  people:Hit (fun j : ℕ × ℕ => (P.activities.forced j.1).support) P.p.B (fun j => Poly.toll w (d.contents.marks j.1 j.2)*D.bill j) (B+1) c
  label : f.Worth w P.p.B (B+1) D.cents u

variable {u a₁ a₂ : ℝ}
local notation "fr" => catalog (R:=R) (P:=P)
include D
lemma buys (H : Bar D B u a₁ a₂) (χ γ : ℝ)(hχ : 1 ≤ χ)(h : χ*(a₁+a₂)+2*u ≤ γ):
    Hit (fr).frame.read P.p.B ((fr).frame.pump (fun i=>Poly.price w (D.coins i)) χ) (B+1) γ:= by
  have ha:0≤B+1:= by linarith [H.above,P.p.exponent_pos]
  let V:Billboard d.contents w P.p.B (B+1) a₁ a₂ := ⟨D.vac,D.bill,D.vac_pos,D.bill_pos,D.vacant,D.cover,H.vac,H.people⟩
  have hf := f.payment D.radii ha H.label
  have hv := V.purchase D.radii ha
  intro x
  let F (i): ℝ:= if x∈ (fr).frame.read i then ((fr).frame.pump (fun j=> Poly.price w (D.coins j)) χ i)* Real.exp ((B+1)*coverNumber P.p.B ((fr).frame.read i)) else 0
  change SumBudget F _
  have he (i : Column R n) : F (.inr i)=(if x∈ Feed.region i then Poly.price w (f.coin D.cents i)*Real.exp ((B+1)*coverNumber P.p.B (Feed.region i)) else 0) := by
    unfold F Letters.Frame.pump Test.coins; rw [if_neg ((fr).inr_hard i)]; rfl
  have hL (i:ℕ) : F (.inl i)=χ*(if x∈(P.activities.forced i).support then Poly.price w (V.merch i)*Real.exp ((B+1)*coverNumber P.p.B (P.activities.forced i).support) else 0):= by
    unfold F Letters.Frame.pump Test.coins; rw [if_pos ((fr).inl_hard i)];
    change (if x∈(P.activities.forced i).support then χ*_*_ else 0)=χ*(if x∈(P.activities.forced i).support then _ else 0); split_ifs
    · exact mul_assoc ..
    exact (mul_zero χ).symm
  refine Cost.enlarge (Cost.sum ?_ ?_) h
  · simp_rw [hL]; exact budget_scale (zero_le_one.trans hχ) (hv x)
  simp_rw [he]; exact hf x

variable [Countable ι]
local instance : Countable (catalog (P:=P) (R:=R)).Patch:=by unfold Shelf.Patch Letters.Frame.Patch; infer_instance

theorem expenses (H : Bar D B u a₁ a₂) (χ γ:ℝ)(hχ : 1≤χ)(h : χ*(a₁+a₂)+2*u≤γ)(hγ:0≤γ)(hg:(P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1):
    let C:= Shelf.Stock.credit fr D.coins
    let x:=stamp D.stock
    x.Sound ∧ (∀ i U, Width.Covered (x.flow i U) (C i)) ∧
      Hit x.span P.p.B (fun i=>Poly.price w (C i)) B ((Real.exp γ-1)/χ):=by
  intro C x
  have hp:=D.check
  have ha : 0≤P.p.supportExponent+1:= by linarith [P.p.exponent_pos]
  refine ⟨stamped D.stock hp.meas_test hp.symtest hp.reads_test (fun i U=>?_ ), D.stock.covered (g:=D.coins) (fun i U=>?_),
     Shelf.Stock.bought fr D.radii (P.p.exponent_pos.le.trans H.above) hχ hγ (buys D B H χ γ hχ h) hg⟩
  · rcases i with i|i
    · exact (D.toBillboard.silent D.radii ha D.articles i U) ▸ Complex.ofReal_im _
    exact f.admitted ..
  rcases i with i|i
  · exact (D.toBillboard.qual D.radii ha i U).receipts
  exact f.funded D.radii ha D.sufficesStamp D.budget i U

variable [Fintype V][Nonempty V]
lemma coupons (S : Bar D B u a₁ a₂)(e:Deck R P)(HA:Accessible P) (χ γ : ℝ)(hχ:1≤χ)(h:χ*(a₁+a₂)+2*u ≤ γ)(hγ:0≤γ)(hg:(P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ)≤1):
    let C:=Shelf.Stock.credit fr D.coins
    let X k:=(P.activities.forced k).support
    let f:=Article.voucher (R:=R) (wharf (p:=P.p) (W:=fr) P HA) d.contents.origins (X ∘ (wharf (p:=P.p) (W:=fr) P HA)) C -- geometry uses x.span via Hosting
    let T:=(D.task HA e).contents
    (∀ k, 0 ≤ f k ∧ ∀ U, ‖T.entries k.1 k.2 U‖ ≤ f k) ∧
    (Hit (fun i : ℕ×ℕ=> X i.1) P.p.B (fun k : ℕ×ℕ=> Poly.toll w (T.marks k.1 k.2)*f k) B ((Real.exp γ-1)/χ)) ∧
    ∀ i, SumBudget (per P.p.B B w (fun k : ℕ×ℕ=> T.marks k.1 k.2) (fun k : ℕ×ℕ=> X k.1) f i) ((Real.exp γ-1)/χ):=by
  intro C Y f T
  let slot:=wharf (W:=fr) (p:=P.p) P HA
  let x:=stamp D.stock
  obtain ⟨ed,cost,hH⟩:= expenses D B S χ γ hχ h hγ hg -- wrong notation
  let he:=wharf_fit P D.stock HA rfl rfl
  have hr: x.span=Y ∘ slot:= funext he.equal_span
  have h:= Reserve.supplier x e.contents slot he ed D.radii cost S.above hH
  change (∀ i j, _ ∧ _)∧_∧_ at h
  rw [hr] at h
  refine ⟨fun i=> ⟨(h.1 i.1 i.2).1,fun U=> ((h.1 i.1 i.2).2 U).1⟩,h.2⟩
end YM.RG3.Script.Reserve
