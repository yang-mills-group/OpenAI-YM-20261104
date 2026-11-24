import YM.OPE.Mountains.Inlet
import YM.OPE.Log.Scales
/-!
# Phase price at joint nested scales

Use subpower precision at leaps (strict exp rate); use grade drop at the root
only when its collapse time is positive in this CURRENT remaining T, which
thus may be much smaller than original T. The root-level drop never needs an
estimate on analytic continuations of a character's particular multipoint
cost on a shell. Only the `throughout` reads for the *unselected* coefficients
are paid with this grade's polynomial-log prices. Insertions then preserve
the costs for every viewer. This avoids any interchanging analytic and Ward/phase
requirements in the log strengthening. Exponential-rate starters and statistical
log estimates from comparisons in `Assembly`, `Log/Peak`, etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Mountain
open Function Filter Finset OPE.Log
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
    {P:Prescription U.sector.derivatives} (hP:P.Coherent)
variable (H:Services C F S) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (hf:φ ≤ F.fuse)
    {W r d}(V:LogPackage C W r d) (hG:MatrixTicket (C:=C) S U.sector.derivatives φ)
variable {I J K:Type}[Fintype I][Fintype J] {s:Arboreal I} {χ:Ultrafilter K} {t:I→ℝ}
    {x:K→I→ E4}{R:K→I→ℝ}{M δ:ℝ}{i j k o:I} {a b : Finset I} {Y:K→J→E4}
    (L:K→Viewers U) (p:I→ C.book.Token) (q:J→ C.book.Token)(n:ℕ)(w:Mode U.sector.derivatives)
variable (h:s.Coterie (χ:Filter K) t M δ x R) (he:Backdrop (χ:Filter K) (fun i=> x i s.root) Y)
local notation "T!"=> (fun i=>s.fullLife (R i))
local notation "u!"=> (fun j=> s.fee p (R j) s.leaves s.root (n+1))
local notation "Φ"=> U.sector.derivatives
local notation "Ψ"=> (fun i=> spectator U (L i))
local notation "v!"=> (fun i n=> flux P (spectator U (L i)) s.leaves (x i) p s.root (Y i) q n)

include he H h
lemma ordered_cost : Wallet (χ:Filter K) T! (fun i=> pickOne P (Ψ i) (x i) s.root w (Y i) q):=by
    have hz:= root_inject h he; obtain ⟨c,hc,hV⟩:= he; obtain ⟨r,hr⟩:= spectators U q H hc (P.letter w); apply Wallet.absolute h.time r; filter_upwards [hz,hV] with i hi hx; unfold pickOne; rw [← glance_sees U (L i) _ _ hi]; exact (glance_bound U _ _).trans (hr _ _ hx)
include hf V hG hP
lemma drop_at (hp:0<t s.root): Wallet (χ:Filter K) T! (fun i=> u! i • v! i n):=by
    have hx:= general_flux U p q L h hP H (Action s) he (n+1); have hh:= fee_is p (n+1) h s.leaves s.initial; have hT:=h.time; have hu:= Wallet.of_strict hT ((hh.pays hT).smul hx) (by unfold leaves; push_cast; linarith only [hp]); let F(w:Mode Φ)(i:K):= coalesce P s.leaves (x i) p s.root w * pickOne P (Ψ i) (x i) s.root w (Y i) q; let A:= bands Φ n; let B:= bands Φ (n+1); let u j:=s.fee p (R j) s.leaves s.root (n+1)
    have hv:A⊆ B:=fun i hi=>(full_bands ..).2 (((full_bands ..).1 hi).trans n.le_succ); have hk: Wallet (χ:Filter K) T! (fun i=> u i • ∑ w∈ B\A, F w i):=by
       simp_rw [smul_sum]; apply Wallet.sum h.time; intro w hw; have hf' := mem_sdiff.mp hw; have he': n+1=w.1:= le_antisymm (lt_of_not_ge (fun hx=> hf'.2 ((full_bands ..).2 hx))) ((full_bands ..).1 hf'.1); apply ((throughout U hP H hf V hG p w h s.Action).mul (ordered_cost (P:=P) U H L q w h he)).congr; filter_upwards with i; unfold u F; rw [he', smul_mul_assoc]; -- hf shadow parse
       rfl
    apply (hu.add h.time hk).congr; filter_upwards with i; unfold u; rw [← smul_add]; congr 1; unfold flux Prescription.truncated Prescription.termRead
    change (whole _ _ _ _ _ _- ∑ w∈ B,F w i) + (∑ w∈ B\A,F w i)= whole _ _ _ _ _ _-∑ w∈A,F w i; rw [sum_sdiff_eq_sub hv]; unfold leaves; abel

-- price any flux at any CURRENT frontier, recovered via smaller shape
omit he H h hf V hG hP
def Renewable (s:Arboreal I)(U:Spec.Final C F S)(P:Prescription U.sector.derivatives)(L:K→Viewers U)(χ:Ultrafilter K)(q:J→ C.book.Token)(Y:K→J→ E4)(n:ℕ)(M δ:ℝ): Prop:= ∀ (t:I→ℝ)(x:K→I→E4)(R:K→I→ℝ), Coterie s (χ:Filter K) t M δ x R → Backdrop (χ:Filter K) (fun i=>x i s.root) Y → ∀ p:I→C.book.Token,
        Wallet (χ:Filter K) (fun i=>s.fullLife (R i)) (fun i=> s.fee p (R i) s.leaves s.root (n+1) • flux P (spectator U (L i)) s.leaves (x i) p s.root (Y i) q n)
include h he
lemma renew (ht:s.Active a)(hq: Renewable ht.restrict U P L χ q Y n M δ): Wallet (χ:Filter K) T! (fun j=> s.fee p (R j) (s.live a) s.root (n+1) • flux P (Ψ j) (s.live a) (x j) p s.root (Y j) q n):=by
    let v:=ht.restrict; let p':= ht.restrictedFn p; let g j:= ht.restrictedFn (R j); let X j:= ht.restrictedFn (x j); obtain ⟨t',hv⟩:= ht.stay h
    apply ((hq t' X g hv he p').raise hv.time ((Wallet.id h.time).of_le (hv.time.eventually_ge_atTop 0) (h.space.mono fun _ hi=> ht.smallerT hi.sizes))).congr;
    filter_upwards [overall_injected h he ht] with j hj; exact congrArg₂ (· • ·) (ht.per_fee (n+1) p (R j)) (ht.shine U P n p (L j) (x j) q (Y j) hj)
include U hf V hG hP H
lemma leaps_on (hp:t s.root ≤ 0)(hu:∀ {I:Type}[Fintype I](v:Arboreal I), v.zones.card < s.zones.card→ Renewable v U P L χ q Y n M δ): Wallet (χ:Filter K) T! (fun i=> u! i • v! i n):=by
    let a:=s.zones; let o:= s.root; let x_:=(fun i=> x i o); have hz: ¬s.SingleLayer t a o:=by
       intro hh; have he (j:I)(he:j∈ s.zones): t j=t s.root:= hh j he (s.closure j); have hr :(∑ i∈ s.middle a,s.stepAt t i)=0:= sum_eq_zero (fun i hi=> sub_eq_zero.mpr ((he i (mem_erase.mp hi).2).trans (he _ (s.inward i)).symm)); have hξ:=h.tracked.entire; rw [hr,zero_add] at hξ; exact hp.not_gt (hξ.symm ▸ zero_lt_one) -- replacement
    obtain ⟨i,hi⟩:= Leap.exists hz h (Action s); let b:= s.redact a i; have hv:s.Active b:= redacted (Action s) hi.inner; let s':= hv.restrict; have hξ:= hu s' (show s'.zones.card<s.zones.card from hv.number.trans_lt (redact_gains hi.active)); let F(j:K)(a:Finset I)(p:I→C.book.Token):= flux P (spectator U (L j)) (s.live a) (x j) p s.root (Y j) q n
    let z(j:K):= s.fee p (R j) s.leaves s.root (n+1); let p'(w:Mode Φ):=update p i (P.letter w); let M'(w:Mode Φ)(j:K):= coalesce P (s.inputs a i) (x j) p i w * F j b (p' w)
    have hf'(w:Mode Φ) : Wallet (χ:Filter K) T! (fun i=> z i • M' w i):=by
       have ht(μ:(Mode Φ)):= renew (P:=P) U L (p' μ) q n h he hv hξ
       have hh: Wallet (χ:Filter K) T! (fun j=> (s.fee p (R j) (s.live s.zones) s.root (n+1) • (coalesce P (s.inputs s.zones i) (x j) p i w * F j b (p' w)))):=by
          refine (by simpa only [mul_one] using (multiply_cash (W:=fun _=>(1:ℝ)) p (n+1) h (Action s) hi.inner (P.letter w) (localFee U hP H hf V hG p w h s.Action hi.active (Subset.refl ..)) (F':=fun i=> F i b (p' w)) (by simp only [mul_one]; exact ht w)))
       exact hh
    let c:ℝ:=((n+1:ℕ):ℝ)*t s.root-s.onset t p s.leaves; have hC:RateLE (χ:Filter K) T! z c:= (fee_is p (n+1) h s.leaves s.initial).pays h.time; obtain ⟨m,hm⟩:= ((useful_flux U p q L h hP H s.Action hi he n) (-c-1)).exists
    apply ((Wallet.of_strict h.time (hC.smul hm) (by linarith only)).add h.time (Wallet.sum h.time (s:=bands Φ m) (fun w _=>hf' w))).congr; filter_upwards with j; rw [← smul_sum,← smul_add]; change z j • ((F j a p-∑ w∈ bands Φ m,M' w j)+∑ w∈bands Φ m,M' w j)= z j • F j a p; rw [sub_add_cancel]

omit h he
variable (M δ χ Y) -- filter coercion complaining var Y section implicit? use binder
lemma issuing (k:ℕ) : ∀ (I:Type)[Fintype I](s:Arboreal I), s.zones.card=k→ Renewable s U P L χ q Y n M δ:=by
    induction k using Nat.strong_induction_on with
    | h k ih=>
      intro I _ s hk t x r h he p; by_cases hi:0<t s.root; · exact drop_at U hP H hf V hG L p q n h he hi
      exact leaps_on U hP H hf V hG L p q n h he (le_of_not_gt hi) (fun s' h=> ih s'.zones.card (hk ▸ h) _ _ rfl)
variable {M δ χ Y}
include h he
lemma all_flux : Wallet (χ:Filter K) T! (fun i=> u! i • v! i n) := issuing U hP H hf V hG χ M δ Y L q n s.zones.card I s rfl t x R h he p
end YM.OPE.Arboreal.Mountain
