import YM.RG16.GaugeCredit.Fall

/-!
# Origin compression consumer on a single copy -- the soft window

Telescope rendered formal stable track against the ACTUAL recurrence over
actual `fitting`; read at the true terminal below the shorter window. Inputs
include a priced MULTI-MATCH on the whole clustered density at b (not just
matching each numerical singleton column), and local defects on analytic
stable propagation. No assumptions on analytic transmission of captured
ERROR states.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG16.Guarding
open Function Filter Set Lattice Wilson RG Source Bid MeasureTheory OPE MergeProof
open Pert Trace.Physical Trace.Physical.GermGraph Literal Work.G08
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}(C:Family G)(H:C.Makes)(N p d k:ℕ)
set_option quotPrecheck false
local notation "S" => C.labels.level d
local notation "X" => measuring C d N p
local notation "s" => (S).coeffSize
local notation "𝓣" => precredit C N p d k
local notation "q" => (fun i:ℕ=>(factor C i)^(-rate))
local notation "τ" => transition (C:=C) d N p
local notation "R" => Prequote C H N p d k
local notation "V" => calValues (C:=C) d N p
local notation "t₀" => mCost C d N p

variable (Z:∀ i,Config G (C.side i p)→ℂ)(w:ℕ→C.label d)(Y:Chart C p d)
local notation "map₀" => (fun i:ℕ=>funded C H N p d i (w i))
abbrev Moves (b j:ℕ)(D:ℝ) := (∀ i≥j,i≤b→ accepted C N p d i (Z i) 0) ∧ (∀ i≥j, i<b→ Foreground C d N p i (τ i (Z (i+1)) - (Y i (w i) + Z i)) D)
abbrev Abooks (b:ℕ)(f:Cut C N p) (D : ℝ): Prop := Foreground C d N p b (precredit C N p d k f b - (Y b (w b) + Z b)) D
abbrev Stamped (i:ℕ)(f:Cut C N p) (e:ℝ) : Prop:= Nullity C N p d i (𝓣 f i - V i (R f i)-Z i) e
variable {f:Cut C N p} {u j i b:ℕ} {e e' D s' r δ γ γ₀:ℝ}

lemma upload (h : Grown C N p d i e Y)(hp:Opened C d i p)(hi:i≤ N){g:Config G (C.side i p)→ℂ}
    (he: Foreground C d N p i (g-(Y i (w i)+Z i)) D) :
   ∃ x:C.label d, t₀ i x ≤ D ∧ Nullity C N p d i (g-(V i (map₀ i+x)+Z i)) (D+e*s (w i)):= by
   let y:= map₀ i; have hy : X i y=w i:= fund_as C H N p d hi hp (w i); have h' := h y
   rw [show mCost C d N p i y=s (X i y) from rfl,hy] at h'
   obtain ⟨x,hx,hq⟩:= foreground_splits he H hp hi; refine ⟨x,hx,?_⟩
   rw [cal_add d N p i H hp.post hi]
   apply Eq.mp _ (Nullity.combine hq (Nullity.neg h' H hp.post hi) H hp.post hi); apply congr_arg (fun f=> Nullity C N p d i f _)
   change _ = g - (V i y+V i x+Z i); abel

lemma preparation (he:Grown C N p d b e Y)(hp:Opened C d b p)(hN:b ≤ N)(hx:accepted C N p d b (Z b) 0)(hy:Booked C N p d f b hN)
    (hm:Abooks C N p d k Z w Y b f D): t₀ b (R f b-map₀ b) ≤ D ∧ Stamped C H N p d k Z b f (D+e*s (w b)):= by
   obtain ⟨x,h1,hX⟩:= upload C H N p d Z w Y he hp hN hm
   have hf : R f b=map₀ b+x:= pred_of C H N p d f hp hN hy (b:=𝓣 f b- (V b (map₀ b+x)+Z b)+Z b) (by simpa only [zero_add] using ((Ink.pred hX).combine hx H hp hN)) (by abel)
   unfold Stamped; rw [hf,add_sub_cancel_left,sub_sub]; exact ⟨h1,hX⟩

lemma saved (he:Stamped C H N p d k Z i f e)(hq:Nullity C N p d i (Z i) r)(hp:Opened C d i p)(hi:i≤N) :
   Nullity C N p d i (𝓣 f i-V i (R f i)) (e+r) := by
   have h:= Nullity.combine he hq H hp.post hi; simpa only [sub_add_cancel] using h

lemma cook (H₀:Moves C N p d Z w Y b j D)(hf:Continuous f)(hp:j≤ i)(hg:i<b)
    (hT:Opened C d i p)(hZ:Opened C d (i+1) p)(ht:b≤N)(hi:Grown C N p d i e Y)
    (hF: Booked C N p d f i (hg.le.trans ht))
    (hG:Gate C d N p i γ 1)(hx:Stamped C H N p d k Z (i+1) f e') :
    t₀ i (R f i - (map₀ i + R f (i+1))) ≤ D+q i*e' ∧ Stamped C H N p d k Z i f (D+e*s (w i)+q i*e'):= by
    let hN:= hg.trans_le ht; let B (i:ℕ):= 𝓣 f i; let y:= map₀ i; let t:= R f (i+1); let v:= B (i+1)-V (i+1) t-Z (i+1)
    obtain ⟨x,h1,he⟩:= upload C H N p d Z w Y hi hT hN.le (H₀.2 i hp hg)
    obtain ⟨x',h2,hA⟩:= nullity_toss v hG hx
    have hu:= Nullity.combine he hA H hT.post hN.le
    let C₀:= (τ i (Z (i+1))-(V i (y+x)+Z i))+(τ i v - V i x')
    have hSeen : B i= V i (y+t+(x+x')) + C₀+Z i := by
        have hs:= Ink.message H hZ.post hN hx
        obtain ⟨_,hq⟩:= H₀.1 (i+1) (hp.trans i.le_succ) hg
        have hx := Ink.message H hZ.post hN hq; have hy:= Ink.message H hZ.post hN (Ink.invest H hZ hN t)
        have hh: B (i+1)=v+(V (i+1) t + Z (i+1)):= by unfold v; abel
        rw [show B i= τ i (B (i+1)) from pre_step C N p d f hf hN,hh,transition_add d N p (u:=v) (v:=V (i+1) t+Z (i+1)) hs (hy.add hx),transition_add d N p hy hx,← factory_eq d N p i H hT.post hN t]
        unfold C₀; simp only [cal_add d N p i H hT.post hN.le]; abel
    change Nullity C N p d i C₀ _ at hu
    have ht' : R f i=y+t+(x+x'):= pred_of C H N p d f hT hN.le hF (b:=C₀+Z i) (by simpa only [zero_add] using (Ink.pred hu|>.combine (H₀.1 i hp hg.le) H hT hN.le)) (hSeen.trans (by abel))
    refine ⟨?_,?_⟩
    · change t₀ i (R f i-(y+t)) ≤ _; rw [ht',add_sub_cancel_left]; exact (mCost_add C H N p d hT hN.le x x').trans (add_le_add h1 h2)
    unfold Stamped; rw [ht',show 𝓣 f i= _ from hSeen]; convert hu using 1; abel

section
variable {Y Z w}
lemma tender (H₀:Moves C N p d Z w Y b j D)(hf:Continuous f)
    (hn:e≥0)(hb:b≤k)(hk:k ≤ N)(hG:Region C N p d j k γ)
    (hF:∀ i, j≤ i → ∀ h0:i≤ b,Booked C N p d f i (h0.trans (hb.trans hk))) (hγ:0 ≤ γ)
    (hA:Abooks C N p d k Z w Y b f D) (hY:∀ i ≥ j, i ≤ b → Grown C N p d i e Y ∧ s (w i) ≤ r) (hD:0≤D)
    (ht: j≤ i)(hh:i≤b):
    Stamped C H N p d k Z i f (2*(D+e*r)) ∧
      mCost C d N p k (R f i- ∑ u∈ Finset.Icc i b,map₀ u) ≤
        (↑b+1-(i:ℝ))*(2*(D+e*r))*hike C j k γ := by
    have hP:= hb.trans hk
    have hj:=ht.trans (hh.trans hb)
    have hpk :Opened C d k p:= hG.openGate k hj le_rfl; let T:= hike C j k γ
    have hy'(i:ℕ)(hi:j≤ i)(hw:i≤k):hike C i k γ≤ hike C j k γ:= Real.rpow_le_rpow (div_nonneg (C.S.a_pos i).le (C.S.a_pos k).le) (div_le_div_of_nonneg_right (C.S.strictAnti.antitone hi) (C.S.a_pos _).le) hγ
    have hr':0≤r:=(size_nonneg _ _).trans ((hY i ht hh).2)
    have he := mul_nonneg hn hr'; let u:= D+e*r; have hW:0≤u:=add_nonneg hD he
    induction hh using Nat.decreasingInduction with
    | self =>
        obtain ⟨h1,h2⟩:= hY b ht le_rfl; have hs:= hG.openGate _ ht hb
        obtain ⟨h,hX⟩:= preparation C H N p d k Z w Y h1 hs hP (H₀.1 b ht le_rfl) (hF b ht le_rfl) hA
        have hδ:= mul_le_mul (hy' b ht hb) h (size_nonneg _ _) (hike_pos C j k γ).le
        have hl:= hike_cost C N p d hG ht hb le_rfl (R f b - map₀ b)
        refine ⟨Ink.inc hX (by linarith only [hW,hD,he,mul_le_mul_of_nonneg_left h2 hn]),?_⟩
        simp only [Finset.Icc_self, Finset.sum_singleton]; apply le_trans hl; refine hδ.trans ?_
        linarith only [mul_le_mul_of_nonneg_left (show D ≤ 2*(D+e*r) by linarith only [hD,he]) (hike_pos C j k γ).le]
    | of_succ i hh ih =>
        have hi: i < k:= hh.trans_le hb; let v:= i+1; have hs:= ht.trans i.le_succ; specialize ih hs
        obtain ⟨h1,h2⟩:= hY i ht hh.le
        have hL := factor_positive C i
        have ht' := hG.cut i ht hi; have hy:0≤ q i:=Real.rpow_nonneg (zero_le_one.trans hL.le) _
        have hx : q i ≤ 1/2 := (le_mul_of_one_le_right hy (Real.one_le_rpow hL.le hγ)).trans ht'
        have hz : q i*(2*u) ≤ u:= by have hT:= mul_le_mul_of_nonneg_right hx hW; linarith only [hT]
        obtain ⟨h3,h4⟩:= cook C H N p d k Z w Y H₀ hf ht hh (hG.openGate i ht hi.le) (hG.openGate _ hs hi) hP h1 (hF i ht hh.le) (hG.cross i ht hi) ih.1
        refine ⟨Ink.inc h4 ?_,?_⟩
        · unfold u at hz; linarith only [hz,he,mul_le_mul_of_nonneg_left h2 hn]
        have hδ : t₀ k (R f i-(map₀ i+R f (i+1))) ≤ T*(2*u):= (hike_cost C N p d hG ht hi.le le_rfl _).trans <| mul_le_mul (hy' i ht hi.le) (h3.trans (by unfold u at *; linarith only [hz,he])) (size_nonneg ..) (hike_pos C j k γ).le
        let ψ i:=∑ l∈Finset.Icc i b,map₀ l; have hq : ψ i=map₀ i+ψ (i+1):= by
           unfold ψ; rw [show Finset.Icc i b = insert i (Finset.Icc (i+1) b) from by ext;simp;omega, Finset.sum_insert]
           simp
        change t₀ k (R f i- ψ i) ≤ _
        rw [hq, show R f i-(map₀ i+ψ (i+1))= (R f i-(map₀ i+R f (i+1)))+(R f (i+1)-ψ (i+1)) from by abel]
        apply (mCost_add C H N p d hpk hk _ _).trans; exact (add_le_add hδ ih.2).trans_eq (by unfold T u; push_cast; ring)

/-- Cap AFTER pursuing shorter analytic comparison; real tail and young
return prices paid separately. In `s` at k, no forward multiplication of
credits (that would not meet these prices). Quantitative, no fixed background
profile/size assumpt. -/
lemma acceleration (H₀:Moves C N p d Z w Y b j D)(hf:Continuous f)(hG:Region C N p d j k γ)
    (hp:Region C N p d u k γ₀)(hn:e≥0)(hb:b≤k)(hk:k ≤ N)
    (hF:∀ i, u≤ i → ∀ h0:i≤ b,Booked C N p d f i (h0.trans (hb.trans hk))) (hγ:0 ≤ γ)
    (hA:Abooks C N p d k Z w Y b f D) (hY:∀ i ≥ j, i ≤ b → Grown C N p d i e Y ∧ s (w i) ≤ r)
    (hW:Nullity C N p d b (Z b) δ) (hD:0≤D) (ht: u≤ j)(hh:j≤b):
    mCost C d N p k (R f u - ∑ u∈ Finset.Icc j b,map₀ u) ≤
      (↑b+1-(j:ℝ))*(2*(D+e*r))*hike C j k γ + 2 * hike C j k γ₀*(hike C b j rate*(D+e*r+δ)) := by
    let y (i):=map₀ i
    have hY':= hY b hh le_rfl
    have hN:= hb.trans hk
    have he:= preparation C H N p d k Z w Y hY'.1 (hp.openGate b (ht.trans hh) hb) hN (H₀.1 b hh le_rfl) (hF b (ht.trans hh) le_rfl) hA
    have hz:= tender C H N p d k H₀ hf hn hb hk hG (fun i h hi=>hF i (ht.trans h) hi) hγ hA hY hD le_rfl hh
    have h' := (tail C H N p d f hf hp hb hk (saved C H N p d k Z (Ink.inc he.2 (add_le_add le_rfl (mul_le_mul_of_nonneg_left hY'.2 hn))) hW (hp.openGate b (ht.trans hh) hb) hN) hF ht hh)
    rw [show R f u-∑ l∈Finset.Icc j b, map₀ l=(R f j-∑ l∈Finset.Icc j b,map₀ l) + (R f u-R f j) from by abel]
    exact (mCost_add C H N p d (hp.openGate k (ht.trans (hh.trans hb)) le_rfl) hk _ _).trans (add_le_add hz.2 h')
end
end YM.RG16.Guarding
