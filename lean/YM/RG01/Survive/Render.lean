import YM.RG01.Survive.Leaves

/-! # Exact second-log rendering and bound before re-expression

Select each of the bounded-support survivors from the SAME origins as
Vacuum.onFloral. Supply a finite coefficient prescription through m on
the common joint leaf kernels (with a last slot charged at m+1 which
retains all errors there). This file compares the rendered log to the
canonically truncated transmission, and reconstructs and bounds the error
on a representation of the actual full density. Explicit residual physical
premises: extension and pricing of the leaf kernels as `LeafReady` (open
for most of the actual leaves), fit of the resulting tariff/Sailor/Ready
and flat funding of the cost at some g-inverse-power disk with any needed
fixed power allocation (only specific tariffs bought in `Vacuum.Actual`).
Consumers still need identifications of the rendered polynomial, stencil
and label alignment beyond the inspected physical ones, calibration with
all scalar and reset effects, and the marked extension. Do not use this to
transfer a canonical residual already aligned to some other labels. Only
on close inspection agreement with the survivor predicate in Vacuum.rare,
see complement theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Survive
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}

/-- Keep survivors of the actual integrated log under the same masks.
Allows common representation across addresses via genuine alliance.
-/
def remain (X:Match.Alliance I H 1 0) (K : ℕ)(ℓ γ : ℝ):Collection.Source G c :=
    Vacuum.weigh I X χ (fun z=>if short K ℓ z then 1 else 0) true γ

def rebate (X:Match.Alliance I H 1 0) (K:ℕ)(ℓ γ:ℝ) {M}(g:Expansions H M)(keepScalar:Bool) (consume : ℕ→Prop): Collection.Source G c where
  logRead :=
    let F : Magazine I → Config G c→ℝ := Sum.elim
      (fun i=> (-1:ℝ) • share (fun _ q => consume q) g K ℓ (X.furrow i))
      (fun (i : Songbook c)=> (if keepScalar then (1:ℝ) else 0) • opus I X χ γ (Sum.inr i))
    choir F ∘ pennant I
  hardRead := (plusone I X χ γ).hardRead

variable {v ρ w δ β a : ℝ}{j K n M : ℕ}{ℓ : ℝ}{g : Expansions H M}{x : H.ThinP→Orders M→ℝ}{z : H.ThinP→ℝ}
    (h:LeafReady χ K ℓ g v j x z ρ) (X:Match.Alliance I H 1 0) (γ : ℝ)
include h
lemma subtract (take : ℕ→Prop) : (remain H (χ:=χ) X K ℓ γ).logRead=
    (rebate H (χ:=χ) X K ℓ γ g true (fun q=> ¬take q)).logRead + (rebate H (χ:=χ) X K ℓ γ g false take).logRead := by
  funext i U
  let j:= pennant I i; let V:= j.1.view U
  simp only [remain, Vacuum.weightedReading, Pi.add_apply, Pi.smul_apply, smul_eq_mul, rebate, plusone,Function.comp_apply,choir]
  unfold Vacuum.weightAt
  generalize hu : pennant I i=l
  rcases l with ⟨i,t|t⟩
  · dsimp only [Prod.fst, Prod.snd, ite_true, Sum.elim, opus,Song.sequence,Pi.smul_apply,Function.comp_apply,smul_eq_mul]
    let P:=X.furrow t; let V:=i.view U
    have hv:= h.recover (fun _ q=>take q) P V
    split
    next hx=> rw [if_pos hx] at hv; rw [show stream H χ (Seat.view i U) _= _ from hv]; ring
    next hx=> rw [if_neg hx] at hv; dsimp only [P,V] at hv; linear_combination (norm := ring) -(Rim c)*hv
  simp

-- inherit catalogue movements by rebuilding function on same seat orbit, K unaffected.
omit h
private lemma localChoice {s' : Collection.Source G c} {p : BudgetPoint}
    (sCurve : Magazine I → Config G c→ℝ)
    (hE:s'.logRead= choir sCurve ∘ pennant I)(hF:s'.hardRead= (plusone I X χ γ).hardRead)
    (b:ℝ) (hB:∃ (k:Magazine I→ℝ), Quotes.early p (scaleT p I) k b∧ ∀ i,p.Regular (scaleT p I i).support (sCurve i)∧
        p.supBounds (scaleT p I i).site (scaleT p I i).support (sCurve i) (k i))
    (hH: Collection.Local (posting p I) p (remain H (χ:=χ) X K ℓ γ) a w):
      Collection.Local (posting p I) p s' (turnFee p*b) w:= by
  obtain ⟨k,hk,hK⟩:=hB
  obtain ⟨hD,hT⟩:=spiral _ _ k (fun i=> (hK i).1) (fun i=> (hK i).2) hk
  obtain ⟨hm,hG,hM,h0,hz⟩:=hH
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; rw [hE]; exact (hD (pennant I i)).1
  · obtain ⟨h,hK',hM,hM',hL,hL',hp⟩:=hG
    change ({reg:= (posting p I).reg, forced:=_, E:= s'.logRead,K:=s'.hardRead}:Activities G c).ForcedFamily p
    rw [hF]
    exact ⟨h,hK',hM,hM',hL,hL',hp⟩
  · intro a b
    have ht:= H.laws.intake.cap.labels.moves a (S.ratio.embed b)
    obtain ⟨σ⟩:= ht
    obtain ⟨η,hη⟩:=settles I X χ a b σ
    let e:=Song.whirl (ι:=Magazine I) a b; let y:=pennant I; let l:=Refrain.badge I
    have hk i:l (congo l η i)=_:=perch l η i; have ha i:y (congo y e i)=_:=perch y e i
    let h x:=spirit (scaleT p I) sCurve a b x
    unfold Listing.read; rw [hE,hF]
    refine ⟨⟨congo y e,congo l η,fun i=>?_,fun i=>?_,fun i=>?_,fun i=>?_,fun i V=>?_,fun i V=>?_,fun i V=>?_⟩⟩
    · change (revolve _ (y (congo y e i))).site=_; rw [ha]; exact (h _).1
    · change (revolve _ (y (congo y e i))).support=_; rw [ha]; exact (h _).2.1
    · change (reserve I (l (congo l η i))).support=_; rw [hk]; exact (hη _).1
    · change (reserve I (l (congo l η i))).inventory=_; rw [hk]; exact (hη _).2.1
    · change (reserve I (l (congo l η i))).extraTest V ↔ _; rw [hk]; exact ((hη (l i)).2.2 V).1
    · change choir sCurve (y (congo y e i)) V=_; rw [ha]; exact congr_fun (h (y i)).2.2 V
    change fuse I X χ (l (congo l η i)) V=_; rw [hk]; exact ((hη (l i)).2.2 V).2
  · rw [hE]; exact ⟨_,fun i=>(hD (pennant I i)).2,fun x=> Cost.equiv (pennant I) (hT x)⟩
  rw [hF]; exact hz

include h
variable (p:BudgetPoint)
    (hs:p.threshold=Pressure.temp s)(hp:p.B=radiusB s)(hi:p.order≤j)(n:ℕ)(hn:p.power≤n)
    (q:ℝ)(hq:0≤q)(hS:Sailor G p.threshold q j)(hr:j*q≤v)(hv:0<v)
    (hA: Quotes.preExponent p ≤ a)(hδ:0<δ)(hY:Ready H.smallAt p.B (fun i=>2^j*z i) (a+δ) w δ β)

include hs hp hi hn hq hS hr hv hA hδ hY

set_option maxHeartbeats 400000 in
/-- Intersect the fitted angular envelopes with the inherited actual order
and move to E6 heights. Require admissibility through post-block power
and tail. Includes canonically rendered truncated polynomial minus all
higher joint letter products in the same pre-reset representation. -/
theorem secondBook (take : ℕ→Prop)(r:ℕ)(he:∀ i,take i → r ≤ i)
    {F B:ℝ}(h0: Collection.Local (posting p I) p (remain H (χ:=χ) X K ℓ γ) F B):
    let u:=rebate H (χ:=χ) X K ℓ γ g false take
    let s:= (ρ^r)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹))
    Collection.Local (posting p I) p u (turnFee p*s) B:=by
  have hf:= h.clearing (H:=H) (fun _ i => take i) p w δ β a hs hp hi n hn q hq hS hr hv hA hδ hY r (fun _=>he)
  intro A t
  let f i:= (ρ^r)⁻¹*LeafReady.allowance p i j n z
  let k:Magazine I →ℝ:=Sum.elim (fun i=>f (X.furrow i)) (fun _=>0)
  let W i:=(-1:ℝ) • share (fun _ q => take q) g K ℓ (X.furrow i)
  let V:Magazine I → Config G c→ℝ:=Sum.elim W (fun _=>0)
  have hW : A.logRead= choir V ∘ pennant I:= by unfold A rebate V; dsimp only; simp [W]
  apply localChoice _ _ _ V hW (by unfold A; rfl) _ ?_ h0 -- h parameter implicit? include h currently unneeded
  have hy (z) := h.germs (χ:=χ) (fun _ i=>take i) (X.furrow z) p hs hi hp q hq hS hr hv n hn (Song.locate I z).site (show (Song.locate I z).site∈Song.perf H (X.furrow z) from (Song.reconnects I X z) ▸ (Song.locate I z).anchor) r he
    (fun i=> nonneg_of_mul_nonneg_right (hY.2.2.2.2.1 i) (by positivity : (0:ℝ)<2^j))
  have hX (m:Magazine I):p.Regular (scaleT p I m).support (V m)∧p.supBounds (scaleT p I m).site (scaleT p I m).support (V m) (k m):=by
    rcases m with m|m
    · have hh:= (hy m).2
      have hs: (scaleT p I (.inl m)).support=reachability (X.furrow m):= reconnects I X _
      rw [hs]; exact ⟨CouplingShape.reg_scale _ (hy m).1,by simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) hh⟩
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(scaleT p I (.inr m)).support) (o:=(scaleT p I (.inr m)).site) 0)⟩
  -- aperture was bought at hit-site from LeafReady.clearing but only anchored at locate H,
  -- and I/H locate choose may (by Classical choice) depend on proof? perf equality + PI choose => anchors same!
  have ht x:(locate I x).site=(locate H (X.furrow x)).site:= by
    let e (S:Support c)(h:S.Nonempty):Site c:= Classical.choose h
    change e (perf I x) _= e (perf H (X.furrow x)) _
    generalize_proofs h1 h2
    have h3 (S T:Support c)(he:S=T)(h1:S.Nonempty)(h2:T.Nonempty) : e S h1=e T h2:=by subst T; rfl
    exact h3 _ _ (Song.reconnects I X x) h1 h2
  refine ⟨k,fun i=> ?_,hX⟩
  rw [← add_zero t]; apply Cost.sum
  · change SumBudget (fun m => if (locate I m).site = i then k (.inl m) * Real.exp (preExponent p*coverNumber p.B (locate I m).support) else 0) t
    let g (m:H.fragrances) := if (locate H m).site=i then f m*Real.exp (preExponent p*coverNumber p.B (locate H m).support) else 0
    rw [show (fun m => if (locate I m).site=i then k (.inl m) * Real.exp (preExponent p*coverNumber p.B (locate I m).support) else 0)=fun m=>g (X.furrow m) from ?_]
    · exact Cost.equiv _ (hf.1 i)
    ext1 m
    unfold g
    by_cases he:(locate I m).site=i
    · rw [if_pos he,if_pos ((ht m).symm.trans he),show (locate I m).support=(locate H (X.furrow m)).support from reconnects I X _]; rfl
    rw [if_neg he,if_neg (fun v=>he ((ht m).trans v))]
  simp [SumBudget,k]


abbrev readerCost {G : Gauge} (p:BudgetPoint) (j n:ℕ) (ρ δ s w β:ℝ)(m:ℕ) := turnFee p * ((ρ^m)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹)))

/-- Exact full product and reassembled in-band error on the SAME representation
even with last (virtual grade M+1) residual entries in the products. Pointwise
in true physical fields and before reset. Need Bishop/winding & marked extension
for consumer declaring curvature or connected multipoint costs. -/
theorem survival (r:ℕ)(_hrM:r≤M) {F B:ℝ}
    (h0 : Collection.Local (posting p I) p (remain H (χ:=χ) X K ℓ γ) F B)
    (path:PathData G)(clip:Clip)(b t₀ Θ : ℝ):
    let t:=readerCost (G:=G) p j n ρ δ s w β (r+1)
    let D:= remain H (χ:=χ) X K ℓ γ
    let A:= rebate H (χ:=χ) X K ℓ γ g true (fun q=> ¬r+1≤q)
    let Y:= rebate H (χ:=χ) X K ℓ γ g false (fun q=> r+1≤q)
    let Z:= posting p I
    D.logRead=A.logRead+Y.logRead ∧ D.hardRead=A.hardRead ∧ D.hardRead=Y.hardRead ∧
      Collection.Local Z p Y t B ∧ (Z.read A).EBound p (F+t) ∧
        earlyValue Z path clip p D b t₀ Θ= earlyValue Z path clip p A b t₀ Θ* Vacuum.exponentialShare Z p Y := by
  intro t D A Y Z
  have hy:=secondBook H h X γ p hs hp hi n hn q hq hS hr hv hA hδ hY (fun q=>r+1≤q) (r+1) (fun _ h=>h) h0
  have hx:D.logRead=A.logRead+Y.logRead:= subtract H h X γ _
  have hz (i):A.logRead i=D.logRead i - Y.logRead i := eq_sub_of_add_eq (show A.logRead i + Y.logRead i= D.logRead i from Eq.symm (congr_fun hx i))
  have hb : (Z.read A).EBound p (F+t):= by
    obtain ⟨a,ha,he⟩:= h0.unweighted
    obtain ⟨y',hy',hT⟩:= hy.unweighted
    have h₁ i: p.supBounds (Z.reg i).site (Z.reg i).support (A.logRead i) (a i+y' i):= by
      rw [hz i]
      exact CouplingShape.sup_sub (h0.smooth i) (hy.smooth i) (ha i) (hy' i)
    refine ⟨_,h₁,fun i=>?_⟩
    let r i':=Z.reg i'
    convert! budget_plus (he i) (hT i) using 1; ext i'; unfold BudgetPoint.mass; dsimp [Listing.read]; split_ifs <;> ring
  exact ⟨hx,rfl,rfl,hy,hb,Vacuum.earlySplit hx rfl _ _ _ _ _ hb hy.unweighted⟩

omit h hs hp hi hn hq hS hr hv hA hδ hY in
lemma noLast (k : ℕ)(h:k≤M)(u:H.fragrances)(q:Option (Fin u.fst)→Orders M) (hp:atGrade (z:=u) q ≤ k) (i) : q i ≠ Fin.last (M+1) := by
  have hq : (q i).1 ≤ k := (single_le_sum (s:=univ) (f:=fun i=> (q i).1) (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hp
  intro hi; rw [hi] at hq; change M+1 ≤ k at hq; omega
end YM.RG01.Survive
