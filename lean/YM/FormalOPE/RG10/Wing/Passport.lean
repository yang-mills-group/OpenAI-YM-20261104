import YM.FormalOPE.RG10.Wing.Quest
/-!
 # Ephemeral Schedule financed on every episode
 Orientation held native $h$ age and prepared constants not merely post-cost. Y budgets for common coupling.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Passenger
open Function PowerSeries Finset Route Cycle HStein Submarine GaugeGear Dispatch Transit
open scoped Topology BigOperators Classical
variable {X I B : Type}
variable {U J:ℕ→ Type} [∀ i,Fintype (U i)] [∀ i,DecidableEq (U i)] [∀ i,Fintype (J i)]
variable (V:Voyage U J)(W:Scale X U)(F: Tier) (G : ∀ i,Subring (Channel (U i)))
variable {b N k d δ:ℕ} {R C γ:ℝ}
/-- Raw-tape Ward & abundance hypotheses. *Additional* demand on pre-block constants
 spelled out explicitly (`fees`). Require Activated educators incl first slot budget before
 all poses and ages. Only names through-order, not analytic families.Time sampling.Trusted.
 Does not give `Regular`; derives it.Moment n appropriate by F and post `Voyage.regular`.
 `Schur` spending from Inventory. Also requires Gauge.Auth.P pass. -/
structure Galaxy (V:Voyage U J)(W:Scale X U)(F:Tier)(G:∀ i,Subring (Channel (U i)))
 (R C γ:ℝ) (δ b N k d:ℕ): Prop extends Hours W R C δ b N where
 up : 0 ≤ γ
 limit : γ ≤ 1
 plenty : (↑(loft k d):ℝ)≤ C^2
 invariant : V.authentic G b N
 fees : ∀ i∈Ico b N,∃ B : ℝ, ∃ p: U (i+1)⊕ U i→ Channel (U (i+1)⊕ U i),
     Activate (V.sail i) p k d (W.point (i+1)) (W.point i) (W.zoom i) F (W.Y C R i^δ) B ∧
     ∀ Q∈ G (i+1),Guard Q k d →
        Through k (kick p ((replot (mark (B:= U i))) Q)) 0 ∧ ∀ x∈ GaugeGear.upstairs k d,cargo Q x≠0 → (2*B)^x.2 ≤ W.fade γ (i+1) i
variable {V W F G}
local notation "Y"=> W.Y C R
local notation "δx"=> δ*expand k -- notation precedence!!
-- rank policy lemma with no-frame
variable {α M : ℝ}
lemma prepayment (a:ℕ) (ha:2≤a)(hα:α≤1)(hc : 0 ≤ M) (ht : (2*M)^2≤α) : (2*M)^a ≤ α:= by
 refine (pow_le_pow_of_le_one (by positivity) ?_ ha).trans ht; nlinarith -- inspect
lemma prepayment1 (a:ℕ) (ha:0<a)(hα:α≤1) (hc : 0 ≤ M) (ht : 2*M ≤ α): (2*M)^a ≤ α:= by
 apply le_trans (pow_le_pow_of_le_one (show 0≤2*M by positivity) (ht.trans hα) ha) ?_; simpa using ht
variable (O:Rally W)
variable (H:Galaxy V W F G R C γ δ b N k d)
private lemma earn (δ k:ℕ): δ ≤ δ * expand k := by have hx:= exponent k; nlinarith

include H O
lemma galaxy : PassBook V W G F O R C γ (δ*expand k) b N k d := by
 refine ⟨PassBook.moved H.toHours (earn ..),H.up,H.limit,H.plenty, H.invariant, fun i hi=>?_, fun i hi=>?_⟩
 · obtain ⟨B,p,hx,he⟩:= H.fees i hi; exact hx.stock.le
 obtain ⟨B,p,hx,he⟩:= H.fees i hi; let w:= Submarine.alternate (V.sail i).spur p k
 obtain ⟨h1,h2,h3⟩:= Dispatch.home hx (O.read i) (G (i+1)) (fun Q h1 h2=>(he Q h1 h2).1)
 rw [←pow_mul] at h1; exact ⟨B,w,h1,h2,fun Q h h'=> ⟨h3 Q h h',(he Q h h').2⟩⟩
local notation "M++"=> PassBook.arrived k (δ * expand k) d
-- diamond gauge.L also any larger.Possale.Ages
variable {i j:ℕ}
lemma destinations (hi : b ≤ i) (hj:i≤j) (he:j ≤ N) (P:Channel (U j)) (hp:P∈G j) (ht:Guard P k d):
  F.gain (audible O i) (V.yield i j P) k ≤ Y j ^(PassBook.arrived k (δ*expand k) d)*F.gain (audible O j) P k ∧
  F.gain (audible O i) (decap (V.yield i j P)) k ≤ W.fade γ j i * Y j ^ (PassBook.arrived k (δ*expand k) d)* F.gain (audible O j) (decap P) k := by
 have ht' := galaxy O H; exact ⟨ht'.family hi hj he hp ht, ht'.dynasty hi hj he hp ht⟩

omit O H
/-- Completes the `stable` field of formal Regular from SAME polynomial(moment n) grade.C.
 Still also requires the separate join supplies (activated currency didn't require all of those
 nor compatibility of RG step implementations and their tracker forecasts). No estimate in actual
 regime. Need uniform F still & Announces.BR.Stamps. -/
lemma arrives (A:Lens W.tape)(n:ℕ)(h:Galaxy V W (Tier.pol n) G R C γ δ b N k d) (hc : ∀ i∈ Ico b N,V.regular W k d n i (Y i^δ)):
   Regular V W R C (δ*expand k + PassBook.arrived k (δ*expand k) d) b N k d n G A:=
 PassBook.arranged (galaxy (Rally.native W A) h) (fun i hi=> PassBook.grant (hc i hi) (pow_le_pow_right₀ (le_trans (by norm_num) (h.toHours.richAt (mem_Ico.mp hi).1)) (earn ..))) -- order
end YM.FormalOPE.RG10.Wing.Passenger
