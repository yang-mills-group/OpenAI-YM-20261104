import YM.Trace.Physicalv2.GermLedger
import YM.Trace.Physicalv2.GermSplit

/-!
Partial comparison across an arbitrary live interval on the Wilson measure.
This is a stability estimate for the one-slot error on the same represented
trajectory. `Foreground` is a local bound on the inhomogeneity itself, not an
assumption of dominant coefficients; the model comparison will need to certify
it with power-of-coupling bills on the requested packets. Keep the labels y
separate from their *true*, generally different numerical germ coordinates at
each level. No assumption of a linear rule for unmasked stable parts of the
compression, just invariant value under an exact re-extension. Uses one and
the same vacuum channel on both sides. Does not yet handle extension to a union
of active roots.
-/
noncomputable section
namespace YM.Trace.Physical.GermGraph
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations
open Push.Local ProjectorNext.Equivariance MeasureTheory Extra.Histories Relay
open Germ Bid Work.G08 PhysicalNext.Repeat.Lotus YM.MergeProof Motion
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option synthInstance.maxHeartbeats 180000
set_option quotPrecheck false
set_option warningAsError false
set_option maxRecDepth 5500
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
variable {G:Gauge}(C:Family G)(d N p:ℕ)
local notation "L" => factor C
local notation "W!" => (C.factory d N p).entries
local notation "G₀" => calValues (C:=C) d N p
local notation "a!" => transition (C:=C) d N p
local notation "E₀" => value (C:=C) d N p
local notation "F" => C.labels.level d
abbrev Er : Type := ∀ i, Config G (C.side i p) → ℂ
abbrev measuring i (y:C.label d) := page d p i (W! i y)
abbrev mCost i (y:C.label d):=(F).coeffSize (measuring C d N p i y)
local notation "X" => mCost C d N p
local notation "PP" => measuring C d N p

abbrev store (i:ℕ):Type:= Coefficient F (C.side i p)
local notation "W₀" => store C d p
-- N not included by lean
structure Shot (err:Er C p) (i:ℕ) (q:W₀ i) (y:C.label d) (r:ℝ) : Prop where
   ready : reads d N p i q r
   zero : page d p i q=0
   detailed : err i=E₀ i q+G₀ i y

def Foreground(i:ℕ)(f:Config G (C.side i p)→ℂ)(D:ℝ) : Prop := ∃ (e:ℝ) (q:W₀ i), 0 ≤ e ∧ reads d N p i q e ∧ (F).coeffSize q.x ≤ e ∧ E₀ i q=f ∧ (1+4*stock C i)*e ≤ D

lemma measuring_sub (H:C.Makes) {m:ℕ}(h:Opened C d m p)(hi:m≤N)(x y:C.label d): PP m (x-y)=PP m x - PP m y:=(fitting d N p m H h hi).map_sub ..
lemma measuring_add (H:C.Makes) {m:ℕ}(h:Opened C d m p)(hi:m≤N)(x y:C.label d): PP m (x+y)=PP m x + PP m y:=(fitting d N p m H h hi).map_add ..
local notation "qu" => (fun i:ℕ=>L i^(-rate))
local notation "vm" => (fun i:ℕ=>fun γ:ℝ=>L i^γ)
def Gate (m:ℕ) (γ ε:ℝ) : Prop := (∀ x:C.label d, X (m+1) x ≤ vm m γ * X m x) ∧ ∀ (q₁ : W₀ (m+1)) r', reads d N p (m+1) q₁ r' → page d p (m+1) q₁=0 → ∃ (v:W₀ m) (x:C.label d), reads d N p m v (L m ^(-rate)*r') ∧ page d p m v=0 ∧ (L m)^rate * X m x ≤ ε * r' ∧ a! m (E₀ (m+1) q₁) = E₀ m v + G₀ m x

lemma card_step {m:ℕ}(H:C.Makes){err f:Er C p}{q:W₀ (m+1)}{y:C.label d}{r γ D ε:ℝ}
    (hm:m<N)(h:Opened C d m p)(hs:Opened C d (m+1) p)
    (hh:Gate C d N p m γ ε)
    (hIn:Shot C d N p err (m+1) q y r) (hT: err m=a! m (err (m+1)) + f m)(ht:Foreground C d N p m (f m) D):
    ∃ (s:W₀ m) (y':C.label d), Shot C d N p err m s y' (qu m*r+D) ∧ (F).coeffSize (PP m y'-PP m y) ≤ (ε*qu m*r+D) ∧ X (m+1) y ≤ vm m γ * (X m y'+ε*qu m*r+D) := by
    obtain ⟨a,g,ha₀,ha,hax,haf,hE⟩:=ht
    obtain ⟨s₀,l,h₁,h₂,h₃,h₄⟩:=hh.2 _ r hIn.ready hIn.zero
    have hl:0<L m:=zero_lt_one.trans (factor_positive C _)
    have hz:0<L m^rate :=Real.rpow_pos_of_pos hl _
    have hQ : X m l ≤ ε*qu m*r:=by
         have hx : L m^(-rate) = (L m^rate)⁻¹:=Real.rpow_neg hl.le _
         rw [show ε*qu m*r = ε*r/(L m^rate) from by rw [show qu m=(L m ^ rate)⁻¹ from hx]; ring]; exact (le_div_iff₀ hz).mpr (by rw [mul_comm]; exact h₃)
    obtain ⟨s',v,h'₁,h'₂,h'₃,h'₄,h'₅⟩:=fresh_split H h hm.le g ha hax
    change X m v ≤ _ at h'₅
    let s:=beside s₀ s'
    let y' := y+l+v
    obtain ⟨hS,hR⟩:= presentation h₁.1 h₁.2 h'₁.1 h'₁.2
    let rr:= (L m^(-rate)*r)+(1+4*stock C m)*a
    have hzero:page d p m s=0:=by unfold s; rw [addPage d N p m s₀ s' H h.post hm.le h₁ h'₁,h₂,h'₂,add_zero]
    have heq : err m=E₀ m s+G₀ m y' := by
        rw [show E₀ m s=E₀ m s₀+E₀ m s' from plus (H.wilson.represents N p m hm.le).good h₁.2 h'₁.2 (C.localSection d)]
        have ht': Integrable (E₀ (m+1) q) (prior G _):=message d N p (m+1) H (h.post.trans m.le_succ) hm hIn.ready
        have hi : Integrable (G₀ (m+1) y) (prior G _):=message d N p (m+1) H hs.post hm (entryOk d N p (m+1) H hs.post hm y)
        rw [hT, hIn.detailed, transition_add d N p (i:=m) ht' hi, h₄, ←factory_eq d N p m H h.post hm, ←haf, h'₃]
        change _ = E₀ m s₀ + E₀ m s'+ G₀ m (y+l+v); rw [cal_add d N p m H h.post hm.le,cal_add d N p m H h.post hm.le]; abel
    have hp: (F).coeffSize (PP m y'-PP m y) ≤ (ε*qu m*r+D):=by
       have h2 :2*a ≤D:=le_trans (mul_le_mul_of_nonneg_right (show 2 ≤ 1+4*stock C m by have := (stage C m).columns_ge; change _ ≤ _+_*((stage C m).columns);linarith) ha₀) hE
       unfold y'; rw [measuring_add _ _ _ _ H h hm.le,measuring_add _ _ _ _ H h hm.le]
       have hident : PP m y + PP m l + PP m v - PP m y = PP m l+ PP m v := by abel
       rw [hident]; exact (Size.add F _ _).trans (add_le_add hQ (h'₅.trans h2))
    refine ⟨s,y',⟨⟨hS,rem_increase d hR (add_le_add le_rfl hE)⟩,hzero,heq⟩,hp,(hh.1 y).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hl.le _))⟩
    rw [show X m y'+ε*qu m*r+D=X m y'+(ε*qu m*r+D) from by ring]
    exact le_trans (b:=(F).coeffSize (PP m y' - (PP m y'-PP m y))) (by rw [sub_sub_self]) ((count_sub ..).trans (add_le_add le_rfl hp))

lemma message_graph (H:YM.MergeProof.Ribbons.Materials C){γ ε:ℝ}(hγ:0<γ)(he:0<ε):∀ᶠ t:ℕ in Filter.atTop, ∀ m≥t, ∀ p N:ℕ, m<N →
   (Opened C d m p ∧ Opened C d (m+1) p) ∧ Gate C d N p m γ ε:= by
     obtain ⟨i,hi⟩:=eventually_atTop.mp (live_graph C d H γ ε hγ he)
     filter_upwards [eventually_ge_atTop i] with t hh m ht p N hm; obtain ⟨hA,hB,h⟩:=hi m (hh.trans ht) p N hm
     exact ⟨⟨hA,hB⟩,h⟩
local notation "Late!" => Gate C d N p
structure Traveling(t top:ℕ) (err:Er C p) (r:ℕ→ℝ)(q:∀ i,W₀ i)(y:ℕ→C.label d)(D ε γ:ℝ) : Prop where
   shot (i) : t ≤ i → i ≤ top → Shot C d N p err i (q i) (y i) (r i)
   step (i) : t ≤ i → i<top → r i ≤ qu i*r (i+1)+D ∧ X (i+1) (y (i+1)) ≤ vm i γ * (X i (y i)+ε*qu i*r (i+1)+D)

lemma traverse (H:C.Makes){err f:Er C p}{r γ D ε t top}(ht:t ≤top)(htN:top≤N)
    (hG:∀ i≥t, i<top→ (Opened C d i p ∧ Opened C d (i+1) p) ∧ Late! i γ ε) (hf:∀ i≥t,i<top→Foreground C d N p i (f i) D)(hT:∀ i≥t,i<top→ err i = a! i (err (i+1)) + f i)
    {v:W₀ top}{x:C.label d} (hA:Shot C d N p err top v x r) :
    ∃ (rs:ℕ→ℝ)(Q:∀ i,W₀ i)(y:ℕ→C.label d), rs top=r ∧ Traveling C d N p t top err rs Q y D ε γ:= by
     induction ht using Nat.decreasingInduction
     case self=>
       let Q:=update (fun i=>W! i x) top v
       have hv : Q top=v:=update_self ..
       exact ⟨Function.const _ r,Q,Function.const _ x,rfl, ⟨fun i hi hh=>by rw [le_antisymm hh hi,hv];expose_names; exact hA,fun i hi h=>False.elim (hi.not_gt h)⟩⟩
     case of_succ i hi IH =>
       obtain ⟨rs,Q,y,hr,hq⟩:=IH (fun j hj hU=> hG j (i.le_succ.trans hj) hU) (fun j hj hU=> hf j (i.le_succ.trans hj) hU) (fun j hj hU=> hT j (i.le_succ.trans hj) hU)
       let hTop:=hq.shot (i+1) le_rfl hi
       obtain ⟨⟨ho,hs⟩,hh⟩:=hG i le_rfl hi
       obtain ⟨s,y',hb,hx,hv⟩:=card_step C d N p H (hi.trans_le htN) ho hs hh (hq.shot (i+1) le_rfl hi) (hT i le_rfl hi) (hf i le_rfl hi)
       let freshR:=qu i*rs (i+1)+D
       refine ⟨update rs i freshR,update Q i s,update y i y', by rw [update_of_ne hi.ne',hr], ⟨?_,?_⟩⟩
       · intro j hj hh
         rcases hj.eq_or_lt with h|h; subst j; simpa only [update_self] using hb
         simp only [update_of_ne (Ne.symm h.ne)]; exact hq.shot _ h hh
       · intro j hj hh
         rcases hj.eq_or_lt with h|h; subst j; simp only [update_self,update_of_ne (Nat.succ_ne_self _)] -- exact
         exact ⟨le_rfl,hv⟩
         simp only [update_of_ne (Ne.symm h.ne),update_of_ne (Ne.symm (Nat.lt_succ_of_lt h).ne)]; exact hq.step _ h hh

/-- Boundary condition at t at the level of the density germ: need not give
bounds on remainder cost here, just finiteness. An amputation by filtered
primary coefficients would instead use invertibility of `fitting`. -/
def Anchored (i:ℕ)(err:Er C p)(b:ℝ):Prop:= ∃ (q:W₀ i) (r:ℝ), reads d N p i q r ∧ (F).coeffSize (page d p i q) ≤ b ∧ err i =ᶠ[𝓝 1] E₀ i q
lemma shot_nn (err:Er C p)(i:ℕ){q y r}(h:Shot C d N p err i q y r): 0≤r:=by obtain ⟨a,b,ha,hb,ht,-⟩:=h.ready.2; linarith
lemma anchored_back (H:C.Makes){p N t b}(hi:Opened C d t p)(htN:t≤N)(err:Er C p)(r:ℝ){q y}
    (hh: Anchored C d N p t err b)(hs:Shot C d N p err t q y r) : mCost C d N p t y ≤ b:=by
    obtain ⟨s,e,he,hB,hEq⟩:=hh
    rw [hs.detailed] at hEq
    change (F).coeffSize (fitting d N p t H hi htN y) ≤ _; rw [←forget_page H hi htN hs.ready hs.zero he hEq.symm]; exact hB
lemma crossing (H:YM.MergeProof.Ribbons.Materials C){γ ε:ℝ}(hγ:0<γ)(hγ':γ<rate)(he:0<ε)(hε':ε ≤ 1) : ∀ᶠ t : ℕ in atTop, ∀ p N, ∀ {D R b:ℝ}{top:ℕ}{err f:Er C p}, t ≤ top → top ≤ N → 0≤D →
    (∀ i≥t, i<top→Foreground C d N p i (f i) D ∧ err i= transition (C:=C) d N p i (err (i+1))+f i) →
    (Anchored C d N p t err b) → (∃ (q:store C d p top) (x:C.label d), Shot C d N p err top q x R) →
    ∃ (Q:∀ i,store C d p i)(y:ℕ→C.label d), ∀ i≥t,i≤top→ Shot C d N p err i (Q i) (y i) (hike C top i rate*R+2*D) ∧ mCost C d N p i (y i) ≤ hike C t i γ*(b+2*((i:ℝ)-t)*D)+2*ε*hike C top i rate*R:=by
    obtain ⟨a,ha⟩:=eventually_atTop.mp (factor_cap C hγ.le hγ')
    filter_upwards [eventually_ge_atTop a,message_graph C d H hγ he,open_late C H.hG d] with t ha' hv hO p N D R b top err f ht htN hD hF hco ht'
    obtain ⟨q,y₀,hq⟩:=ht'
    obtain ⟨r,Q,y,hR,hq⟩:=traverse C d N p H.makes ht htN (fun j hj he=>hv j hj _ _ (he.trans_le htN)) (fun i hi h↦ (hF i hi h).1) (fun i hi h↦(hF i hi h).2) hq
    have ha' := ha t ha'
    let s (i:ℕ):=mCost C d N p i (y i)
    have hX:s t ≤ b:=anchored_back C d H.makes (hO _) (ht.trans htN) err (r t) hco (hq.shot _ le_rfl ht)
    have hS:=across_est C hγ.le ht (shot_nn C d N p err top (hq.shot top ht le_rfl)) he.le hε' hD ha' (show ∀ i ≥ t,i<top → _∧_ from hq.step) hX
    refine ⟨Q,y,fun i hi hh=>?_⟩
    obtain ⟨hg,hs₀,hs₁⟩:=hq.shot i hi hh
    refine ⟨⟨⟨hg.1,rem_increase d hg.2 ((hS.1 _ hi hh).trans ?_)⟩,hs₀,hs₁⟩,?_⟩
    · rw [hR]
    · have hh':= hS.2 _ hi hh; rw [hR] at hh'; exact hh'
end YM.Trace.Physical.GermGraph
