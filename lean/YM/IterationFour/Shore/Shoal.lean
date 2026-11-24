import YM.IterationFour.Shore.Break

/-!
# Pinned iteration consumer on original layouts, all scales
    Finite R, startup and α shift same person. Marks don't need to ever
    propagate on another Rep instance now. Lens includes enough to reconstruct
    pre- and post E_H every step. Require stronger data on budgeted Ω keys
    when needed from stamps also, don't infer a branch uses the balance sheet
    except for the Y produced.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Shore
open Lattice Wilson RG Function MeasureTheory Filter Vacuum AnalyticBridge VerifiedReset Collection Ovens
open Progress.DirectedRecipe Averaging Extra.Iteration Currency
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C : Family G}{r N q m i : ℕ}
local notation "a#"=> C.path.levels
local notation "T#"=> C.path.rep N q
local notation "S#"=> C.path.levels.params

/-- With an output iteration budget, Surf permits reading the rendered packet
    E-alignment everywhere needed with the ACTUAL H marker stamps. The K you
    push with in the comparison still has old supports. When integrating
    W#(input into this exponent) with marked activity on old stamps, pay
    shards by merger of every seed/support incl marked using the old
    alphabet. Equality here uses RAW failure terms and also the small (unwanted)
    adjustment to β, does not change any markers nor eligibility. -/
lemma seeing (h : C.Makes) (hi:i ≤ N) {r : List (Piece G (C.side i q))}{b:RG.Rep G (C.side i q)}{W I γ ℓ q':ℝ} (hh:Surf C N q i r b W q') (hp:Coin C N q i r b I γ ℓ) :
    ∃ X:Shard G (C.side i q), X.Wins (a#.budget i) q' ∧ let A:=T# i; let p:=a#.budget i; ∀ U,
       A.activities.additive p U = b.activities.additive p U + Render.renders (Render.prefactor (g C N q i)) p U r + (b.beta-A.beta)*Push.BetaTransport.kinetic A.path A.clip p U-X.read U := by
   obtain ⟨X,hX,hf⟩:= hh.sets; refine ⟨X,hX,?_⟩; intro A p U
   have he:= hf U
   have hz:=hp.read_exponent h hi U
   let P:=loaded C N q i r b
   have hh : P.activities.additive p U=b.activities.additive p U + Render.renders (Render.prefactor (g C N q i)) p U r:= by
      have he:b.p=p:=hp.types.budget
      rw [← he]; exact Render.additive _ (by rw [he]; exact hp.lives) (by rw [he]; exact hp.error) U -- δ inf
   have hQ:A.p=p:=(h.wilson.represents N q i hi).vac
   have hP : b.clip=A.clip := hp.types.clip.trans (h.wilson.represents N q i hi |>.clip).symm
   rw [hP, hp.types.budget, hp.types.stencil] at hz
   unfold Rep.exponent at he -- also P exponent on rhs; refold
   change A.v*_ -_ -_ = P.exponent U + _ at he
   have he': A.exponent U=P.exponent U+X.read U:= hf U
   have hx: P.exponent U=A.v*_ - (A.path.inChannels A.clip p A.beta U + (b.beta-A.beta)*Push.BetaTransport.kinetic A.path A.clip p U)- P.activities.additive p U:= hz
   have hω:A.exponent U=A.v*Fintype.card (Site (C.side i q)) -A.path.inChannels A.clip p A.beta U-A.activities.additive p U:= by rw [← hQ]; rfl
   linarith only [he',hx,hω,hh]

variable (P: Plan C N q r) (S:Purse)(T:ℕ→Pocket)
def signal i x := (T i).due x (S.guardBill a# (i+1))
/-- Preserve actual old stamps at all these levels. -/
structure Ledger (C:Family G)(N q:ℕ) where
    stamps i : Bank G (C.side i q)
    forms (i:ℕ):i<N → (stamps i).Holds (C.path.rep N q i) -- top not paid by analytic unmarked step, different on H.Vac direct.
    story (i:ℕ): i<N → (stamps i).β=C.path.β N q (i+1)
variable (L:Ledger C N q)

lemma Ledger.pushing (h : C.Makes) (hg:G.Simple) (hi : i<N)
    (hn : WilsonStartup.Decent (S# i).clip (a#.budget i))
    (hσ: Geo.Width (a#.budget i) (S# i).clip (S# i).width) :
    let A:=L.stamps i; let P:=T# i; earlyValue A.X P.path P.clip P.p A.v (T# (i+1)).beta A.τ A.alpha=(a#.clock.op i q).push (T# (i+1)).beta (T# (i+1)).eval:=by
    intro A P
    rw [← show (L.stamps i).β=(T# (i+1)).beta from L.story _ hi]; -- rhs beta!
    funext U
    rw [← show P.eval U=(a#.clock.op i q).push (L.stamps i).β (T# (i+1)).eval U from L.story i hi ▸ congr_fun (h.wilson.steps N q i hi|>.1) U]
    have hp:= h.wilson.represents N q i hi.le
    have hn':20 < (C.side i q).val:= by have ht:=a#.fits.sizeT i q; change _ ≤(C.side i q).val at ht; omega
    exact (Bank.Holds.counted (L.forms i hi) hp.good.paths hg hn' (hp.clip.symm ▸ hp.vac.symm ▸ hn) (hp.clip.symm ▸ hp.vac.symm ▸ hσ) U).2.symm

structure Sale where
    A : ℕ→ℝ -- portion for F.own
    φ : ℕ→ℝ -- portion for χ
    total : ℕ→ℝ -- account total soft H
    hard : ℕ→ℝ -- H.stamp actual K at full p.norm

variable (U:Sale)
structure Perks (m:ℕ): Prop where
    since : ∀ i,m≤ i→i<N→ Room C S P i (T i)  -- funds ordinary merger; use one extra check here
    purse : ∀ i,m ≤ i→ i<N→ ∀ x:ℝ, x ≤ S.limit a# (i+1) → softNeed G (a#.budget i) (S# i).clip (S# i).width (S# i).paths (P.alpha i) (signal (C:=C) S T i x) ≤ U.A i
    charger : ∀ i,m ≤ i→ i<N→ ∃ κ:ℝ, Payments.Rates (a#.budget i).B (T i).forceGoal (T i).forceEarly (U.A i+U.φ i) κ
    all : ∀ i,m ≤ i→i<N→ U.A i+ U.φ i+(L.stamps i).price (T# i) (S# i) ≤ U.total i
    hard : ∀ i,m ≤ i→ i<N→(L.stamps i).γ ≤ U.hard i

/-- Local interface delta from using the Fk prescription. Producer isn't
    required to respond to every possible input along different histories;
    only one density path. May use the supplied receipts, REAL cherry and
    sector calls will need this (β^ not used). `Foam` on actual held step.
    DO NOT extrapolate supports more than requested. -/
structure Peak (m:ℕ):Prop where
    top : ∃ b x, Issued P S T N x b ∧ Surf C N q N (P.layers N) b (U.hard N) (U.total N)
    open_interior : ∀ i,m ≤ i → i<N → ∀ b x, Issued P S T (i+1) x b → Surf C N q (i+1) (P.layers (i+1)) b (U.hard (i+1)) (U.total (i+1)) →
      ∃ Y v τ X, Foam C N q i (P.layers i) (L.stamps i) Y v τ (signal (C:=C) S T i x) (T i).forceEarly (P.alpha i) (P.predict i) (U.φ i) X

/-- Exact assembly retaken before any payments. -/
structure Signal (i:ℕ)(x:ℝ)(W:RG.Rep G (C.side i q))(z:ℝ): Prop where
    since :
      ∃ Y v τ X, Foam C N q i (P.layers i) (L.stamps i) Y v τ (signal (C:=C) S T i x) (T i).forceEarly (P.alpha i) (P.predict i) (U.φ i) X ∧
      W=Render.append (P.layers i) (wheel (T# i).path (S# i).clip (a#.budget i) Y v (P.alpha i) τ (P.predict i) X)
           (Render.prefactor (gain (P.predict i))-Render.prefactor (g C N q i)) ∧
             z=owed a# i (P.layers i) (S.guardBill a# i) (signal (C:=C) S T i x)
structure Army (m:ℕ)(F:Trail (C:=C) (q:=q)): Prop where
    march : ∀ i,m ≤ i→ i<N→ Signal P S T L U i (F.loss (i+1)) (F.atLevel i) (F.loss i)
    returns : ∀ i,m≤ i→i≤N→ Surf C N q i (P.layers i) (F.atLevel i) (U.hard i) (U.total i)
    tallies : ∀ i,m ≤ i→i≤N→ Issued P S T i (F.loss i) (F.atLevel i)

variable {P S T L U}
lemma bought (h : C.Makes) (hg:G.Simple) (H: Perks P S T L U m) (hd:Peak P S T L U m)
    (hw:∀ i≥m,i<N→ FixedWave C i (S.guardBill a# i)) {x b}(hM:m ≤ i) (hi : i<N)
    (hp:Issued P S T (i+1) x b) (hh:Surf C N q (i+1) (P.layers (i+1)) b (U.hard (i+1)) (U.total (i+1))) :
    ∃ W z, Signal P S T L U i x W z ∧ Surf C N q i (P.layers i) W (U.hard i) (U.total i) ∧ Issued P S T i z W:=by
    obtain ⟨Y,v,τ,X,hY⟩:= hd.open_interior i hM hi b x hp hh
    let V:= L.stamps i
    let hS:= H.since i hM hi
    obtain ⟨κ,hκ⟩:= H.charger _ hM hi
    obtain ⟨ha,hP,hZ,h₀,hξ⟩:= Vacuum.limits P S hg hS x hp.nonneg hp.cap
    obtain ⟨hz,⟨he,g,hg',hL⟩,hu⟩:= anchor h hg (L.forms i hi) hY hi.le hS.decent hS.width hS.format (H.purse _ hM hi x hp.cap) hκ hS.predicted (S.guard_pos a# i|>.le) hS.hard_paid (hw i hM hi) ((add_le_add_left hZ _).trans hS.supplies)
    exact ⟨_,_,⟨Y,v,τ,X,hY,rfl,rfl⟩, ⟨Time.K_rises he (H.hard _ hM hi),g,hg'.income (H.all _ hM hi),hL⟩,⟨h₀,hZ,hz,hu.trans hξ⟩⟩

lemma heard (h : C.Makes) (hg:G.Simple) (H: Perks P S T L U m) (hd:Peak P S T L U m)
    (hw:∀ i≥m,i<N→ FixedWave C i (S.guardBill a# i)) (hi: m ≤ N) : ∃ X, Army P S T L U m X:=by
    suffices ∀ i:ℕ,i≤N→ m ≤ i→ ∃ X,Army P S T L U i X from this m hi le_rfl
    intro i hL; induction hL using Nat.decreasingInduction with
    | self=>
        obtain ⟨W,z,h₀,h₁⟩:= hd.top; let X:Trail (C:=C) (q:=q):= ⟨fun _=>z, update (T#) N W⟩; have hk:X.atLevel N=W:= update_self ..; exact fun _=> ⟨X,⟨fun k hk hh=>False.elim (hh.not_ge hk),fun i hi hm=> by rw [show i=N from le_antisymm hm hi,hk]; exact h₁,fun i hi hm=>by rw [show i=N from le_antisymm hm hi,hk]; exact h₀⟩⟩
    | of_succ j hj ih=>
        intro hM; obtain ⟨X,ht⟩:= ih (hM.trans j.le_succ)
        obtain ⟨W,z,hW,hZ,hY⟩:= bought h hg H hd hw hM hj (ht.tallies _ le_rfl hj) (ht.returns _ le_rfl hj)
        let V:Trail (C:=C) (q:=q):= ⟨update X.loss j z, update X.atLevel j W⟩; have hk:V.atLevel j=W:= update_self ..; have he:V.loss j=z:=update_self ..; have ht' i (hi:j< i):V.loss i=X.loss i:=update_of_ne hi.ne' ..; have hL i (hi:j< i):V.atLevel i=X.atLevel i:= update_of_ne hi.ne' ..
        refine ⟨V,⟨fun i hi hm=>?_,fun i hi hm=>?_,fun i hi hm=>?_⟩⟩
        · rcases eq_or_lt_of_le hi with rfl|h₀; · rw [hk,he,ht' _ j.lt_succ_self]; exact hW
          rw [ht' i h₀,ht' _ (h₀.trans i.lt_succ_self),hL i h₀]; exact ht.march _ h₀ hm
        · rcases eq_or_lt_of_le hi with rfl|h₀; · rw [hk]; exact hZ
          rw [hL i h₀]; exact ht.returns _ h₀ hm
        rcases eq_or_lt_of_le hi with rfl|h₀; · rw [hk,he]; exact hY
        rw [ht' i h₀, hL i h₀]; exact ht.tallies _ h₀ hm
end YM.IterationFour.Shore
