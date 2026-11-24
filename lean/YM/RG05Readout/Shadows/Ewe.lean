import YM.RG05Readout.Shadows.Ink
/-!
# Terminal polynomial read on all Root alternatives

The per-center, per-anchor price of the terminal state. Still no volume
assumption, independent of period. This suffices to price Vault on the
replicated path.Branch can then use stock spiker w/o denominator global loss.
Does not assert existence of compatible geometry/authentication.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address Many Pressure
open Legato Bandage Next.Rank.Station Accent Marker Menu Ac Next.Rank Spindle
open GridApprox.Nil Extra.Trajectories Extra.Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N n b m p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ} {x e E a r y z δ k σ τ:ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R₀"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op n p
local notation "L"=> C.S.block n
local notation "F₀" => Palette C d
local notation "κ₁"=> kappa C.path
-- leading wraps thin ≤1
variable (hw:Awake D B b d)
open Finset
section
variable {n:Side} {A:Rep G n}
def coinCost (A:Rep G n) (X:Three G n)(U:Config G n):ℝ:= ‖X.snd.1 U‖ + ∑ i, ‖profile A.activities X.snd.2 i U‖
lemma coin_plus {U:Config G n}{P Q:Three G n}(hr:Useful A P)(hp:Useful A Q):coinCost A (P+Q) U ≤ coinCost A P U+coinCost A Q U:=by
    unfold coinCost; rw [show (P+Q).snd.2=P.snd.2+Q.snd.2 from rfl, MergeProof.Float.prof_add _ hr.normK hp.normK]
    exact (add_le_add (norm_add_le ..) (le_trans (sum_le_sum fun i _=> norm_add_le ..) (le_of_eq (Finset.sum_add_distrib)))).trans_eq (add_add_add_comm ..)
lemma coin_scale {U:Config G n}{P:Three G n} (x:ℂ): coinCost A (x • P) U= ‖x‖*coinCost A P U:=by
    unfold coinCost; rw [show (x • P).snd.2=x • P.snd.2 from rfl,profile_scale]; simp_rw [Pi.smul_apply,norm_smul]; rw [show (x • P).2.1 U=x • P.2.1 U from rfl,norm_smul]; rw [← mul_sum,mul_add] -- simp
lemma coin_many {U:Config G n}{I:Type*}{P:I→ Three G n}(hr:A.Lawful x e a r z)(H:Finset I)(hp:∀ i,Useful A (P i)) : coinCost A (∑ i∈ H,P i) U ≤ ∑ i∈H,coinCost A (P i) U:=by
    induction H using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty]; change ‖(0:ℂ)‖ + (∑ i : Box n, ‖profile A.activities (0:ℕ→Goods G n) i U‖) ≤ _; simp [profile,cram]
    | @insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (coin_plus (hp i) (Useful.family _ hr s _ hp)).trans (add_le_add_right ih _)
lemma coin_after (t:Motion) (x:Site n) {P Q: Three G n}(U:Config G n)(he:Signpost A t x P Q):coinCost A Q U=coinCost A P (Lattice.pull t.1 x U):=by
    unfold coinCost; rw [he.gate, he.lens]; congr 1; exact Motion.norm_scalar t _
    rw [← Equiv.sum_comp (puff t x)]; apply Finset.sum_congr rfl; intro j _; unfold floatUp; rw [Equiv.symm_apply_apply]; exact Motion.norm_scalar t _
end
local notation "p₀"=> (C.path.levels.params b).columns
abbrev colCash (C:Family G)(b:ℕ):=3+(C.path.levels.params b).columns
local notation "Q"=> colCash C b
section
include hw h
local notation "R"=> (R₀ b)
lemma fee_one (hb:b ≤ N) (g:ℕ)(hp:g ≤ d)(P:Coefficient (C.labels.level g) (C.side b p))(hr:P.remBound 0 R (κ₁ b) a) (U:Config G (C.side b p)): coinCost R (invoice P 0 (C.localSection g) R) U ≤ Q*((C.labels.level g).coeffSize P.x+a):=by
    have hk: κ₁ b ≤ 1:= divisor_le C b -- check
    have hy : (R).p=(Z!|>.budget b):= h.wilson.represents N p b hb|>.vac; have hv : 1 ≤ p₀:= Stage.columns_ge _
    have he:= hull (C.localSection g) (R) 0 P U (C:=p₀) (fun i=>by rw [hy]; exact h.priced g b p (hw.post _ hp) 0 i) hr hk (zero_le_one.trans hv)
    let s:= (C.labels.level g).coeffSize P.x
    unfold coinCost; apply le_trans (add_le_add he (tendrils (R) 0 P U hr hk|>.2))
    unfold colCash; have ht:= rem_nonneg hr; nlinarith only [ht,hv,Work.G08.size_nonneg (C.labels.level g) P.x]
variable {φ:Body}
lemma high_fee (hN:b ≤ N)(P:Tape G (C.side b p))(h': Necklace (C.labels.level 0) (C.localSection 0) C.params (R) 0 (κ₁ b) d P a) (U:Config G (C.side b p))(hP: Cap (d+2) φ 1): coinCost R (P φ) U ≤ Q*a:=by
    have hp:=h.wilson.represents N p b hN; have hs : 0≤ Q:=by unfold colCash; linarith only [Stage.columns_ge ((Z!).params b)]
    induction h' with
    | empty => rw [mul_zero]; unfold coinCost; change ‖(0:ℂ)‖+(∑ i:Box (C.side b p),‖profile (R).activities 0 i U‖) ≤ _; simp [profile,cram]
    | @chain V r v t f hf hh u hx hq he ih=>
       rw [LinearMap.add_apply,glyph_apply,mul_add]; refine (coin_plus (Useful.smul (R) _ _ (Useful.invoice _ _ _ _ hp.good hq hx)) (he.works hp.good _)).trans (add_le_add ?_ ih)
       rw [coin_scale]; have hz:= fee_one h hw hN 0 (Nat.zero_le _) u hq U
       have hk:‖f φ‖≤v:= (hh φ 1 hP).trans (le_of_eq (mul_one ..))
       exact (mul_le_mul_of_nonneg_left hz (norm_nonneg _)).trans ((mul_le_mul_of_nonneg_right hk (mul_nonneg hs (add_nonneg (Work.G08.size_nonneg ..) (rem_nonneg hq)))).trans_eq (mul_left_comm ..))

abbrev harvestCost (C:Family G)(d b:ℕ):= (1 + pulseFee d) * colCash C b
local notation "V₀"=> harvestCost C d b
lemma priced (ht:b ≤ N){P:Tape G (C.side b p)}{x y:Palette C d}(hr:Printed C d (R) 0 (κ₁ b) P x y E)(hf:Cap (d+2) φ 1) (U:Config G (C.side b p)) : coinCost R (P φ) U ≤ (harvestCost C d b) * (size x+E):=by
     have hp:= h.wilson.represents N p b ht; have hw0 : 0≤ Q:=by unfold colCash; linarith only [Stage.columns_ge ((Z!).params b)]
     rcases hr with @⟨V,X,k,t,hV,hK,hR,hP,hX,hY,hC⟩
     let f i:= invoice (V i) 0 (C.localSection _) R; let a i:= readJ i 0 φ • f i
     let Y':=∑ i,a i; let c i:= (C.labels.level (kept i)).coeffSize (V i).x; have ha: P φ=Y' + X φ:=by rw [← hP,LinearMap.add_apply,Address.together, LinearMap.sum_apply]; rfl
     have hu i:Useful R (a i):=Useful.smul _ _ _ (Useful.invoice _ _ _ _ hp.good (hR i) (hK i))
     rw [ha]; apply (coin_plus (Useful.family _ hp.good Finset.univ _ hu) (hV.works hp.good φ)).trans
     have hb i:coinCost R (a i) U ≤ pulseFee d * (Q*(c i+k i)):=by unfold a; rw [coin_scale]; apply (mul_le_mul_of_nonneg_left (fee_one h hw ht _ (Nat.sub_le ..) (V i) (hR i) U) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (le_trans (fees _ _ box0 hf) (le_of_eq (mul_one _))) (mul_nonneg hw0 (add_nonneg (show 0≤c i from Work.G08.size_nonneg ..) (rem_nonneg (hR i)))))
     have hv:= (high_fee h hw ht X hV U hf);
     have he:= add_le_add (le_trans (coin_many hp.good Finset.univ hu) (Finset.sum_le_sum (fun i _=> hb i))) hv
     have hE:size x= ∑ i,c i:=by rw [hX, bill_group]
     refine he.trans ?_; rw [← Finset.mul_sum,← Finset.mul_sum, Finset.sum_add_distrib,← hE]; unfold harvestCost; have hT:=hV.nonneg; have hp:=feepos d
     have hz':0 ≤ ∑ i,k i:= Finset.sum_nonneg (fun i _=> rem_nonneg (hR i));
     have h' : pulseFee d* (Q*(size x+(∑ i,k i)+t))≤ pulseFee d*(Q*(size x+E)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show _ ≤ size x+E from by linarith only [hC]) hw0) hp.le; nlinarith only [mul_nonneg (mul_nonneg hp.le hw0) hT,mul_le_mul_of_nonneg_left hC hw0,h',mul_nonneg hw0 hz',mul_nonneg hw0 (size_ge x)]
end
end YM.RG05Readout.Shadow
