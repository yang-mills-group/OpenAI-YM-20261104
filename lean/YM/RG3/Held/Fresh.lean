import YM.RG3.Held.Tensor
import YM.RG3.Forms.Rewrite

/-!
# Uniform merger profile receipt for Ω-held applications

Extract uniform bounds with the exact same post-application View. Shares P,
test locations, clocks and both program dictionaries & costs across Ω; no
assumption of good flags only. This addresses **Ω-test** derivatives by
allowing them as extra inputs priced at the same receipt (multilinearity of
separable tests : `Held.Sources` etc). No authorization for differentiating
through nonlinear masks, coupling threshold etc under this exact identity.
Before comparison/tail estimates keep held vars on their native terms at
the stipulated norm widths.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Held
open Lattice Wilson RG Overlay Marker RG3.Ink RG3.Press RG3.Forms Function MeasureTheory Ac Push.Corrected Finset Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {Ω V I : Type*} [Countable I] [Nonempty V] [Nonempty Ω] [DecidableEq V] [Fintype V] {R : Census V}
variable {G : Gauge} {n : Side} {P : Rep G n}
variable (d : Ω → Deck R P) (L : View Ω V G n P R)
variable (f : Ω → Feed G n R I) (w : V → ℝ)

-- common Ω price x f assumption: same organizations/areas. V origins
-- for L must be same as those of input. No commonality needed on input
-- H stencils for THIS operation. `Ω` supplied on full families for all
-- ur (otherwise use subtype Ω).
structure Inspector (s k E : ℝ) (org : V → Site n) where
  planner (x : Ω) : Forms.Test (d x) (f x) s w k E
  coins : ℕ ⊕ Column R n → Poly R
  shares x : coins = (planner x).coins
  holds x : (d x).contents.origins=org

namespace Inspector
variable {d f w s k E} {org : V→Site n} (Q : Inspector d f w s k E org)
local notation "fr" => catalog (R:=R) (P:=P)
local instance patches : Countable ((catalog (R:=R) (P:=P)).Patch) := by unfold Shelf.Patch Letters.Frame.Patch; infer_instance

def stampPage (x : Ω) : Article (catalog (P:=P) (R:=R)).Patch P.p G R org := {
  -- explicit rebuild instead of cast across holds
  address := (stamp (Q.planner x).stock).address
  flow := (stamp (Q.planner x).stock).flow }

omit [Nonempty V] [Nonempty Ω] [Fintype V] in
private lemma sturdy (x) : (Q.stampPage x).Sound := by
  let H := Q.planner x
  have hp : (stamp H.stock).Sound := stamped H.stock H.check.meas_test H.check.symtest H.check.reads_test (fun i U => by
    rcases i with i|a
    · change ((d x).contents.each i U|>.part R.quiet).im=0
      rw [H.toBillboard.silent H.radii (by linarith [P.p.exponent_pos]) H.articles]; rfl
    exact (f x).admitted _ _)
  refine ⟨?_,hp.ready,hp.honest,hp.query,hp.invariantTest,hp.reads⟩
  intro i
  have he := hp.payload i; nth_rw 1 [Q.holds] at he; exact he

-- pure fixed P version. τ arguments can include test tags/position
-- derivatives when supplied. For nonpure moving vacuum use separate.
variable {χ γ : ℝ}

def stay (h : Accessible P) : View Ω V G n P R := L.impression Q.stampPage (wharf (p:=P.p) P h)

-- certify the uniform transport if P fixed, keeping each published label.
theorem seated (HA : Accessible P)
    (hp : ∀ x, Adjust (d x) (f x) P (⟨L.terms x,(d x).captions⟩ : Deck R P)) -- allow arbitrary caption o below?
    (hLs : L.origins=org)
    {u a : ℝ} (white : ℕ→ℝ)
    (hu : ∀ x i, w i*‖L.global x i‖ ≤ u)
    (hL : ∀ x, Article.Contents (L.terms x))
    (hN : ∀ i,0 ≤ white i ∧ ∀ x z, z∈ (L.rays i).val → P.p.supBounds (org z) (L.branch i) (L.regular x i) (white i))
    (hW : ∀ i, SumBudget (L.costR w white i) a)
    (hχ : 1 ≤ χ) (h : χ*(k+E)+2*s≤γ) (hγ : 0≤γ)
    (green : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1)
    (hs0 : ∀ x i U, ((f x).slip i U).part R.quiet=0)
    (input : ∀ x, ∃ a b c d' e g, (d x).Active ∧ (d x).Budget a b c d' e g)
    (hv : ∃ c, ∀ x, (d x).captions.Paid w P.p c)
    {t b : ℝ} (hδ : (Real.exp γ-1)/χ ≤ t*b) (hb : 0<b) :
    Nonempty ((Q.stay L HA).Passport w u a t b) ∧
      ∀ x, let o : Deck R P := ⟨(Q.stay L HA).terms x,(d x).captions⟩
        o.density=(d x).density ∧ o.contents.origins=(d x).contents.origins := by
  classical
  let p := P.p
  let S := Shelf.Stock.credit (catalog (P:=P) (R:=R)) Q.coins
  let x0 : Ω := Classical.arbitrary Ω
  have hw := (Q.planner x0).radii
  have H0 (x y) : (fr).frame.ground y = _ := (wharf_fit P (Q.planner x).stock HA rfl rfl).equal_span y
  have HH : Hit (fun y => (P.activities.forced (wharf (W:=fr) (p:=p) P HA y)).support) p.B (fun i => Poly.price w (S i)) p.supportExponent ((Real.exp γ-1)/χ) := by
    have hv := Shelf.Stock.bought (fr) hw P.p.exponent_pos.le hχ hγ ((Q.planner x0).offer χ γ hχ h) green
    simp_rw [S,Q.shares x0]
    convert hv using 1
    exact (funext (H0 x0)).symm
  have hA (x) : (Q.stampPage x).Hosting P (wharf (p:=p) P HA) := by
    obtain ⟨hc,ht,hi,hf⟩ := wharf_fit P (Q.planner x).stock HA rfl rfl
    exact ⟨hc,ht,hi,hf⟩
  refine ⟨L.issued Q.stampPage _ hLs Q.sturdy hA S w (fun i x U => ?_) HH hδ hb hw hL white hu ?_ hW,fun x => ?_⟩
  · let Y := Q.planner x
    have he := Y.stock.covered (g:=Y.coins) (fun i U => show Width.Covered _ _ from by
      rcases i with i|i
      · exact (Y.toBillboard.qual hw (by have := p.exponent_pos; linarith [P.p.exponent_pos]) i U).receipts
      exact (f x).funded hw (by linarith [P.p.exponent_pos]) Y.sufficesStamp Y.budget i U) i U
    unfold S; rw [Q.shares x]; exact he
  · rw [hLs]; exact hN
  intro o
  let Y := Q.planner x
  let t' : Deck R P := ⟨L.terms x,(d x).captions⟩
  obtain ⟨_,_,_,_,_,_,hi,HB⟩ := input x
  obtain ⟨c,hv⟩ := hv
  obtain ⟨-,hb',hr⟩ := Y.stay χ γ hχ h hγ green HA (hp x) (hs0 x) HB hi hδ hb (hL x) (show Article.LogBounds t'.contents w u a from
    ⟨hu x,white,fun i => ⟨(hN i).1,fun z hz => by change P.p.supBounds (L.origins z) _ _ _; rw [hLs]; exact (hN i).2 x z hz⟩,hW⟩) (show t'.captions.Sound t'.contents.origins from (hp x).compatible ▸ hi.captions) (hv x)
  constructor
  · change (⟨(Q.stampPage x).impression (L.terms x) (wharf (W:=fr) (p:=p) P HA),(d x).captions⟩ : Deck R P).density=_
    -- inst for pin may differ! local instances Countable fr.Patch are Prop.
    exact hr
  exact (hp x).compatible.symm

end Inspector
end YM.RG3.Held
