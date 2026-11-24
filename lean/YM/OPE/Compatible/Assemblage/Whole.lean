import YM.OPE.Compatible.Assemblage.Fortuna
import YM.Planned.PRIMARY_INTEGRAL_295.East
/-!
# Long coarse segments, either with unit match or on the signed track

Don't need γ itself in the logarithmic budget: buying one extra
true horizon will retain the full desired engineering gains. This lets
us use radii with simple engineering evolution.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Relay
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G}{N p k d i:ℕ} {H:History G} {V:Type}[Fintype V][DecidableEq V]
    {W:Bid.Worth}
-- arbitrary zero-grade frame
lemma solo_unit (F:Labels.Frame G 0)(x:F.Index): x=0:=by
    by_contra hn; have h:= F.factors_pos x hn; have hh:= Planned.PrimaryIntegral295.Film.second_fits F x; omega
lemma only_unit (F:Labels.Frame G 0)(v:F.Coeff)(n:ℕ): v= (v 0) • unitVec F H n:=by
    unfold unitVec; simp only [pow_zero,one_smul]; ext1 i; rw [solo_unit F i]; simp [Labels.Frame.e0]
section zero
variable {F:Labels.Frame G 0}{E:Hol G}{S:SectionData F}{X:Voice F H p i}
lemma turn_circle (he:Heard S H N p E i X) (x:F.Coeff): X.index x=x ∧ X.charge x=0:=by
    have hx : X.index x=x:=by nth_rw 1 [only_unit (H:=H) F x N]; rw [map_smul,he.unit]; refine Eq.trans ?_ (only_unit (H:=H) F x N).symm; simp only [unitVec,pow_zero]
    refine ⟨hx,le_antisymm ((he.cone _).trans_eq ?_) (rem_nonneg (he.earns x|>.2))⟩
    have hv : F.core (X.index x)=0:=by ext1 i; rw [solo_unit F i]; simp [Labels.Frame.core]
    rw [hv]; simp [Labels.Frame.coeffSize]
end zero
-- any params.
variable {u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}
   {D:∀ N p i:ℕ,i<N→GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
set_option quotPrecheck false
section
variable {A :∀ i:ℕ, Solo (C.labels.level 0) C.path p i}{M:Extra.Histories.Music (C.labels.level 0) C.path N p}{y:Coefficient (C.labels.level 0) (C.side k p)}{c₀ Q E w₀:ℝ}
    (h:Fortune C W ψ N p k 0 y c₀ Q E M D A)
    (hp:Sung (C.localSection 0) C.path N p C.params W (C.ref 0) M)
    (hv:y.Format 0 C.params (C.path.rep N p k))(hx:y.remBound 0 (C.path.rep N p k) (Real.sqrt (C.path.levels.clock.forcedAllowance k)) c₀)
include hp h hx
local notation "F"=> C.labels.level 0
local notation "ℓ"=> C.ref 0
lemma ground_bill (hi:ℓ ≤ i)(hk:i≤k): (A i).cost M 0+(F).coeffSize ((A i).bar M 0).x ≤ 3*E:=by
   let b:= (A ℓ).a; let I:= (A i); let V:= (A i).bar M 0; let v:= (A i).bar M (-b); let x:= M.tone i
   have hs:= produces M hp y h hi hk; have he:= hp.earned i hi (hk.trans h.limit); have he'(u): x.charge u=0:= (turn_circle he u).2
   have hf'(u):x.index u=u:= (turn_circle he u).1; have hg:= hp.earned k h.oldest h.limit
   have hV:(F).coeffSize b ≤2*E:= (turn_circle hg b).1 ▸ bias_price M hp y h hx
   have ht(u): ((A i).bar M u).x=(A i).a+u:= (keys (C.localSection 0) C.path N p C.params M u (h.fit.chairs i hi hk) he).1.trans (hf' _)
   have hU: V.x=v.x+b:=by unfold V v; rw [ht,ht]; abel
   have hY:(A i).cost M 0=(A i).cost M (-b):=by unfold Solo.cost; simp_rw [(show ∀ u,(M.tone i).charge u=0 from fun u=>he' u)]
   refine (add_le_add hY.le (show (F).coeffSize V.x≤(F).coeffSize v.x+(F).coeffSize b from hU ▸ (Size.add ..))).trans ?_
   change (A i).cost M (-b)+(F).coeffSize v.x ≤ _ at hs; linarith only [hs,hV]
include hv
omit [Fintype V][DecidableEq V] in
lemma starting_whole {e:V→ Site (C.S.side k p)}{P:Ensemble V} {X:Stem V G (C.S.side k p)} (hX:Stamp (N:=N) P (C.localSection 0) e y X): Stamp (N:=N) P (C.localSection 0) e ((A k).bar M 0) X:=by
    obtain ⟨hf,hu⟩:= expo_on M hp y h 0 hv hx
    have he:= hp.earned k h.oldest h.limit; let I:= M.tone k
    have ht(u):= (he.earns u).2; have h0:= (expoLinear (T:=C.localSection 0) I.plays I.charge he.book ht).mk' _|>.map_zero
    have h1:= (inkL I.plays I.charge he.book ht).mk' _|>.map_zero
    rw [show ((M.tone k).plays 0).exponentialEntry 0 (C.localSection 0) _=0 from h0,add_zero] at hf
    rw [show profile (C.path.rep N p k).activities ((M.tone k).plays 0).forced=0 from h1,add_zero] at hu
    refine ⟨hX.homes,?_,?_⟩; · rw [hf,hX.real']
    unfold sunny; rw [hu]; exact hX.price
omit hv
lemma leading_whole (hS: Scrim C W u ψ φ δ ζ r D)(hw:0<w₀)(hz:∀ i:ℕ,C.ref 0≤ i→i ≤ k→ w₀*(3*E)≤ ζ 0 i) :
    Guided (C.localSection 0) C.params C.path N p (C.ref 0) k (fun i=> (A i).bar M 0) D (fun _=> w₀) :=by
   have h0 := (hS.costs.heights 0 (C.ref 0) N p le_rfl (h.oldest.trans h.limit)).choose_spec.1
   refine singing (C.localSection 0) h.oldest (fun _ _ _=>hw) (fun _ _ _=>le_rfl) h0 (travels M hp y h 0 (ζ 0) ?_); intro i hi ht
   rw [alto_norm,pow_zero, inv_one, mul_one]; exact (mul_le_mul_of_nonneg_left (ground_bill h hp hx hi ht) hw.le).trans (hz i hi ht)
end
-- signed. direction weights
variable {A :∀ i:ℕ, Solo (C.labels.level d) C.path p i}{M:Extra.Histories.Music (C.labels.level d) C.path N p}{y:Coefficient (C.labels.level d) (C.side k p)}{c₀ Q E w₀:ℝ}
    (h:Fortune C W ψ N p k d y c₀ Q E M D A) (hp:Sung (C.localSection d) C.path N p C.params W (C.ref d) M)
def lantern (H:History G) (w:ℝ) (d k i:ℕ):= w*(H.S.a i/H.S.a k)^d
lemma lan_pos (H:History G)(hw:0<w₀):0<lantern H w₀ d k i:= mul_pos hw (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _)
lemma lan_home (H:History G): lantern H w₀ d k k=w₀:=by unfold lantern; rw [div_self (H.S.a_pos _).ne',one_pow,mul_one]
lemma lan_equiv (H:History G): lantern H w₀ d k i* ‖alto H i d‖= w₀*‖alto H k d‖:=by
    unfold lantern; rw [mul_assoc,alto_norm,alto_norm, div_pow]; have hp:= pow_pos (H.S.a_pos i) d; rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hp.ne',one_mul]
lemma lan_ratio (H:History G): (((H.S.block i).val:ℝ))^d * lantern H w₀ d k (i+1)= lantern H w₀ d k i:=by
    unfold lantern; rw [H.S.a_step]; have hp:0 < ((H.S.block i).val:ℝ):=by positivity
    let L:ℝ:=(H.S.block i).val; change L^d*(w₀*_)=_; rw [mul_left_comm, ← mul_pow, ← mul_div_assoc, mul_comm L, div_mul_cancel₀ _ hp.ne']
lemma lan_mono (H:History G)(hw:0<w₀): lantern H w₀ d k (i+1) ≤ lantern H w₀ d k i:=by
    apply le_trans _ (lan_ratio H).le; exact le_mul_of_one_le_left (lan_pos H hw|>.le) (one_le_pow₀ (by exact_mod_cast (H.S.block i).property))
include h hp
lemma filled_signed (hS: Scrim C W u ψ φ δ ζ r D)(hw:0<w₀)(hz:∀ i:ℕ,C.ref d≤ i→ i ≤ k→ w₀ *‖alto C.path k d‖*E≤ ζ d i) :
    let z:=(A (C.ref d)).a
    Club C.path C.params (C.localSection d) (ζ d) ψ (C.ref d) k N p (lantern C.path w₀ d k) D (fun i=> (A i).bar M (-z)) (fun i=> (A i).cost M (-z)) h.limit ∧ Guided (C.localSection d) C.params C.path N p (C.ref d) k (fun i=> (A i).bar M (-z)) D (lantern C.path w₀ d k) :=by
    intro z
    have hh:=travels M hp y h (-z) (ζ d) (w:=lantern C.path w₀ d k) (fun i hi he=> by refine (mul_le_mul_of_nonneg_left (produces M hp y h hi he) (mul_nonneg (lan_pos C.path hw).le (norm_nonneg _))).trans ?_; rw [lan_equiv]; exact hz i hi he)
    refine ⟨hh,singing (C.localSection d) h.oldest (fun _ _ _=> lan_pos C.path hw) (fun _ _ _=> lan_mono C.path hw) ?_ hh⟩
    exact (hS.costs.heights d (C.ref d) N p le_rfl (h.oldest.trans h.limit)).choose_spec.1
end YM.MergeProof.Ribbons.ManyCopies.Stem
