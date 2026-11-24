import YM.IterationFour.Shore.Cushion

/-!
# Alignment exponent on OLD stamps
    Consumer with additive E corrections pre reset (recipient coupled Wilson paths).
    Includes possible differences suppressed by the kinetic test as a separate
    budget on the old R. Exact pointwise. Produces a COIN and keeps exact β
    and labels on OLD R call via Surf; parsing/alignment therefore required on
    concrete old R stamps, not arbitrary equal densities. This variant only needs
    one-use marker-free merger budget at +1 even for that comparison output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Shore
open Lattice Wilson RG Function MeasureTheory Filter Vacuum AnalyticBridge VerifiedReset Collection Ovens
open Progress.DirectedRecipe Averaging Extra.Iteration Currency
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{n : Side}{p : BudgetPoint}
-- allowed for both top & step. At inner step under consideration use the EXISTING stamped proof.
-- For top, might use arbitrary early quantum with specified settlement (or no Bills; Surf directly).
structure Bank (G:Gauge) (n:Side) where
    X : Listing G n
    v : Collection.Source G n
    alpha : ℝ
    τ : ℝ
    β : ℝ
    H : ℝ
    w : ℝ
    δ : ℝ
    γ : ℝ
namespace Bank
variable (T: Bank G n) (b:RG.Rep G n)
structure Holds : Prop where
    stamps : Local T.X b.p T.v T.H T.w
    ingredients : Ingredients (shelves T.X b.path b.p) (branch T.X b.path b.clip b.p T.v T.alpha) b.p T.δ T.γ
    casts : b=finish b.path b.clip b.p (shelves T.X b.path b.p) (branch T.X b.path b.clip b.p T.v T.alpha) (T.β+T.alpha+delta (T.X.read T.v)) (vac T.v T.τ)
abbrev price (S:Stage):= softNeed G b.p b.clip S.width S.paths T.alpha T.H
abbrev much (W:PathData G) (p:BudgetPoint) (c:Clip):= powder (shelves T.X W p) (branch T.X W c p T.v T.alpha)
variable {T b}
lemma Holds.spending (h : T.Holds b) : b.activities.Valid b.p T.δ T.γ :=by
   have ht:= h.ingredients.gates b.path b.clip (T.β+T.alpha+delta (T.X.read T.v)) (vac T.v T.τ)
   rw [← h.casts] at ht; exact ht
lemma Holds.counted {W σ ℓ} (h : T.Holds b)(hp:b.path.Bounds b.clip σ W ℓ) (hg:G.Simple)(hn : 20 < n.val)
    (hc:WilsonStartup.Decent b.clip b.p) (he:Geo.Width b.p b.clip σ) U :
    b.exponent U + (T.much b.path b.p b.clip).read U = old b.path b.clip T.X T.v b.p T.alpha T.β T.τ U ∧ b.eval U = earlyValue T.X b.path b.clip b.p T.v T.β T.τ T.alpha U:=by
   let B:= b.path; let c:= b.clip; let p:= b.p; let u:= shelves T.X B p; let m:= branch T.X B c p T.v T.alpha; let β:= T.β+T.alpha+delta (T.X.read T.v); let s:= vac T.v T.τ; let Y:= finish B c p u m β s
   have hh : b=Y:= h.casts; change b.exponent U+(T.much B p c).read U = old B c T.X T.v p T.alpha T.β T.τ U ∧ b.eval U=earlyValue T.X B c p T.v T.β T.τ T.alpha U; rw [hh]
   exact ⟨((congr_arg (fun x=>x+(T.much B p c).read U) (equal_stamp u m B c p β s U)).trans (h.stamps.exponent hg hp hc he T.alpha hn T.β T.τ U)) , (h.ingredients.unshifted B c β s U).trans (h.stamps.raw_evaluator hg hp hc he T.alpha hn T.β T.τ U)⟩ -- fix
end Bank
section
variable (C:Family G)(N q i:ℕ)(S:List (Piece G (C.side i q)))

local notation "H#"=> C.path
local notation "a#"=> C.path.levels
local notation "r#"=> C.path.rep N q i
/-- Supplies the representation on **r#**, includes E^, R.path & kinetic change and the
    χ; all signs in exponent. Back-inference to cores analytic producer at next level on
    old H K masks. Use Surf.infer or Bank.Books identities before reading the next step.
    COIN only (not proven for an equal density). -/
structure Surf (b : RG.Rep G (C.side i q))(r σ : ℝ) : Prop where
    funds : (r#).activities.KBound (a#.budget i) r
    sets : ∃ X:Shard G (C.side i q), X.Wins (a#.budget i) σ ∧
       ∀ U,(r#).exponent U = (loaded C N q i S b).exponent U + X.read U
variable (T:Bank G (C.side i q))(Y:Listing G (C.side i q))(v:Collection.Source G (C.side i q))
/-- Exact real exponent parse on this old stack. EProd from analytic calls *after* all
    normalization/extraction, retains indicator failures at alignment, compares to finite power,
    no α reset iteration here. Pre stamp β is incoming coupling (for registered family). -/
structure Foam (τ H W α β φ : ℝ) (X : Shard G (C.side i q)): Prop where
    paid : Local Y (a#.budget i) v H W
    sameK : Y.hard=T.X.hard
    sameH : v.hardRead=T.v.hardRead
    absolute : X.Wins (a#.budget i) φ
    settled U : let p:= a#.budget i; let P:=(a#.params i).clip; let r:= r#.path
       old r P T.X T.v p T.alpha T.β T.τ U =
        residualE r P Y v p α β τ U+X.read U-Render.renders (Render.prefactor (gain β)) p U S
variable {C N q i S T Y v}

private lemma gas_pre {T:Bank G n}{Y:Listing G n}{v:Collection.Source G n}(h:Y.hard=T.X.hard) (hp:v.hardRead=T.v.hardRead)
    (U:Config G n):(Y.read v).gas p U= (T.X.read T.v).gas p U:= by
   cases Y; cases v; dsimp only at h hp; cases h; cases hp; rfl

lemma anchor (h : C.Makes) (hg:G.Simple){τ H W α β φ π:ℝ}{X:Shard G (C.side i q)} (hx:T.Holds r#)
    (hh:Foam C N q i S T Y v τ H W α β φ X) (hi:i ≤ N)
    (hn: WilsonStartup.Decent (a#.params i).clip (a#.budget i))
    (hσ: Geo.Width (a#.budget i) (a#.params i).clip (a#.params i).width)
    (hm : Render.permits S (a#.budget i))
    {A κ l : ℝ}
    (ht:softNeed G (a#.budget i) (a#.params i).clip (a#.params i).width (a#.params i).paths α H ≤ A)
    (he:Payments.Rates (a#.budget i).B π W (A+φ) κ)
    (hp: β∈stripe (B a# i)) (hl:0 ≤ l) (hP:π ≤ a#.clock.forcedAllowance i)
    (hw : FixedWave C i l)
    (hy : owed a# i S l H + Render.unitBill S (B a# i) ≤ a#.clock.allowance i) :
    let R:= wheel r#.path (a#.params i).clip (a#.budget i) Y v α τ β X
    let z:= Render.append S R (Render.prefactor (gain β) - Render.prefactor (g C N q i))
    Coin C N q i S z (owed a# i S l H) π l ∧ Surf C N q i S z T.γ (A+φ+T.price r# (a#.params i)) ∧
      |β-C.path.β N q i| ≤ conversion C.path.levels i l H := by
    intro R z
    let p:= a#.budget i; let W':=r#; let c:=(a#.params i).clip; let S':=a#.params i; let Q:=W'.path; let d:=delta (Y.read v); let b:=shelves Y Q p; let t:=Reset.reserve Q c p Y v α d; let x':= Render.append S R (Render.prefactor (gain β))
    have hC:=h.wilson.represents N q i hi
    have hx0 : W'.p=p:= hC.vac; have hC0: W'.clip=c:=hC.clip
    have hc:20 < (C.side i q).val:= by have hv:= a#.fits.sizeT i q; change _ ≤ (C.side i q).val at hv; omega
    have hB : Q.Bounds c S'.width S'.paths (a#.clock.loopCap i):= by rw [← hC0]; exact hC.good.paths
    have hj:= wheel_board hg hc hB hh.paid hn hσ hh.absolute ht he
    let D0:= regularNeed G p c S'.width S'.paths 0 H
    have hv: R.activities.Valid p D0 π:= hj.gates Q c (β+d) (Collection.vac v τ)
    have hCn : W'.activities.KBound p T.γ:= hx0 ▸ hx.spending.boundK
    have hδ: (p).threshold^2* |R.beta - β| ≤ H:= by
       change _ * |β+d-β| ≤ H; rw [add_sub_cancel_left]; exact delta_bound hg hh.paid.projects
    let ξ:= Shard.adds (powder b t) X
    let Tin:= T.much Q p c
    have hA: (powder b t).Wins p A:= Shard.Wins.income (powdering (α:=α) hg hc hB hh.paid hn hσ) ht
    have hξ: ξ.Wins p (A+φ):= Shard.advances hA hh.absolute
    let Uq:= T.price W' S'; let Z:= Shard.adds ξ Tin.dark
    have hψ: Tin.Wins p Uq := by
       have he : WilsonStartup.Decent W'.clip W'.p:= by rw [hx0,hC0]; exact hn
       have hy : Geo.Width W'.p W'.clip S'.width:= by rw [hx0,hC0]; exact hσ
       have hz:= powdering (α:=T.alpha) hg hc hC.good.paths hx.stamps he hy
       unfold Tin p c; rw [← hC.clip, ← hC.vac]; exact hz
    have hK: ∀ U, W'.exponent U+Tin.read U= residualE Q c Y v p α β τ U+X.read U-Render.renders (Render.prefactor (gain β)) p U S ∧ W'.eval U=earlyValue T.X Q c p T.v T.β T.τ T.alpha U:= by
       intro U; have hΩ := hx.counted hC.good.paths hg hc (hC.vac.symm ▸ hC.clip.symm ▸ hn) (hC.vac.symm ▸ hC.clip.symm ▸ hσ) U; rw [hC.vac,hC.clip] at hΩ; exact ⟨hΩ.1.trans (hh.settled U),hΩ.2⟩
    have hf : x'.eval=W'.eval:= by
       funext U; obtain ⟨h₁,h₂⟩:= hK U
       unfold x'; rw [Render.generated (Render.prefactor (gain β)) hm hv U,h₂,appearing]
       have h': R.eval U = Real.exp (residualE Q c Y v p α β τ U+X.read U)*(Y.read v).gas p U:= wheelValue hg hc hB hh.paid hn hσ τ β hh.absolute hj U
       rw [h',mul_right_comm _ ((Y.read v).gas p U), ← Real.exp_add, hh.settled,gas_pre hh.sameK hh.sameH,← sub_eq_add_neg]; rfl
    have hv': R.activities.Valid p (adjusting a# i * H) π:= by
       have hz:D0=adjusting a# i*H:= by
         simp [D0,Time.table G S' (show Time.Same S' p from ⟨rfl,rfl,rfl⟩),S',c,adjusting]; -- check
       rw [← hz]; exact hv
    obtain ⟨h₁,h₂⟩:= useful C h hi R ⟨rfl,rfl,rfl⟩ hv' hm hp hδ hf hl hw hP hy
    refine ⟨h₁,⟨hCn,Z,Shard.advances hξ (Shard.dark_pay hψ),fun U=>?_⟩,h₂⟩
    let u:=Render.prefactor (G:=G) (n:=C.side i q) (gain β); let w:=Render.prefactor (G:=G) (n:=C.side i q) (g C N q i)
    have hj':R.exponent U + (powder b t).read U=residualE Q c Y v p α β τ U:= jot hg hc hB hh.paid hn hσ τ β X U
    have hv := (hK U).1
    have he:Z.read U=(powder b t).read U + X.read U-Tin.read U:= by
        rw [show Z.read U=ξ.read U+ Tin.dark.read U from Shard.increased hξ (Shard.dark_pay hψ) U, Shard.dark_read, show ξ.read U= _ from Shard.increased hA hh.absolute U]; abel
    rw [he]; have hf : (loaded C N q i S z).exponent U= R.exponent U- Render.renders u p U S:= by
       change R.v * _ - _ - (Render.append S z w).activities.additive p U = R.exponent U-_
       have hx:(Render.append S z w).activities.additive p U=z.activities.additive p U+ Render.renders w p U S:= Render.additive w hm (Render.addition (u-w) hm hv') U
       have hz:z.activities.additive p U=R.activities.additive p U+Render.renders (u-w) p U S:= Render.additive (u-w) hm hv' U
       change R.v * _ - R.path.inChannels R.clip p R.beta U-(Render.append S z w).activities.additive p U = R.v*_ - R.path.inChannels R.clip p R.beta U-R.activities.additive p U - _
       rw [hx,hz,Render.render_sub]; ring
    rw [hf]; change W'.exponent U=_; unfold u; linarith only [hj',hv]
end
end YM.IterationFour.Shore
