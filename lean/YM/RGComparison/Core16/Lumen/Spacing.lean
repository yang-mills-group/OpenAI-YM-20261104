import YM.RGComparison.Core16.Lumen.Rustle
/-!
# Spend free Taylor errors at older Stamp levels uniformly

Supply from smaller coupling order, request ARBITRARY additional world steps, never
from pricing the needed result already. Physical Hoop price includes exposed sensor comp-cost
as `Ticket` not interpreting Theta choices at the point x=0. See `Error.motion`
for real integral engine.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Planet Finset Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {B U V:Stage}{G:Gauge}{D ι L I S k T A: Type}
lemma above_refl : B.Above B:=⟨le_refl _,le_refl _⟩
lemma above_trans (H:U.Above B)(J:V.Above U): V.Above B:=⟨H.1.trans J.1,H.2.trans J.2⟩
lemma clean (B:Stage)(q:ℕ){p:ℝ→Prop}(H: ∀ᶠ s:ℝ in atTop,p s):∃ T:Stage,T.Above B ∧ q≤T.p ∧ ∀ s,T.L≤s→ p s:=by
    rcases eventually_atTop.1 H with ⟨n,hn⟩
    exact ⟨⟨max B.L n,max B.p q,B.high.trans (le_max_left ..)⟩,⟨le_max_left ..,le_max_left ..⟩,le_max_right .., fun _ h=>hn _ ((le_max_right ..).trans h)⟩
lemma buy_both (A B:Stage):∃ T:Stage,T.Above A ∧ T.Above B:=by
    obtain ⟨T,h1,h2,h3⟩ := clean A B.p (eventually_ge_atTop B.L); exact ⟨T,h1,h3 _ (le_refl _),h2⟩

variable [Fintype D] {n:Side} {X:Shelf G A D}
variable [Fintype ι][Fintype k][Fintype T](P:Planet X n ι k T)


def Visit (T:Stage)(X:Shelf G A D):= ∀ s,T.L≤s→ amen X (dollar s)
def Raw (P:Planet X n ι k T)(B:Stage)(r d:ℕ)(c:ℝ) := ∀ u:Rail G ι, u.length ≤ d → B.Ticket r c (fun s=> P.expect (dollar s) (sing u (dollar s)))
namespace Raw
variable {P} {r R d L : ℕ} {c u:ℝ}
omit [Fintype D] in
lemma broaden (H:Raw P B r d c)(h:U.Above B)(hu:u ≥ c)(hd: d ≥ L) : Raw P U r L u:= by intro x hx; exact ((H x (hx.trans hd)).extend h).promote hu
end Raw
omit [Fintype D] in lemma newer (H: Visit B X)(h:U.Above B): Visit U X:= fun s he=> H s (h.gate.trans he)
variable [Fintype L] [Fintype I] {f : Melody G ι} {p: Stuff G ι L} {C u:ℝ}

-- thermal probe compared through rank a, multiplied by this bill; retain
-- residual scalar expectation identity with same term ψ. Lapse = supports the
-- subtraction of exactly the pure moments predicted on one older order.
def lapse (a:ℕ) (p:Stuff G ι L) (ψ:(L→G.Color)→ℝ) (f : Melody G ι) (w:Rail G ι) (s:ℝ):=
    (dollar s)⁻¹^a * P.expect (dollar s) (sing w (dollar s)* Error (a+1) f ψ p (dollar s))

section ticket
variable {P} (H:P.Steady) {a r d N i:ℕ}{ψ:(L→G.Color)→ℝ}{w:Rail G ι} (hp:Visible X ψ f p N C)
include H hp
lemma joinedL {s:ℝ}(h:amen X (dollar s)) :
    lapse P a p ψ f w s = (dollar s)⁻¹^a * P.expect (dollar s) (sing w (dollar s)* Error (r+1+a) f ψ p (dollar s)) +
       ∑ i∈range r, dollar s^(i+1)*P.expect (dollar s) ((sing w*tale p ψ (a+1+i)) (dollar s)) := by
    unfold lapse; simp_rw [Error.tribute H hp h]; let g := dollar s; have hg:0<g:=dollar_pos _
    let F j:= P.expect g ((sing w*tale p ψ j) g)
    rw [show r+1+a=a+1+r by omega,sum_range_add _ (a+1) r]
    let W:= ∑ i∈range r,g^(i+1)*F (a+1+i); let A:= ∑ i∈range r,g^(a+1+i)*F (a+1+i)
    have hz: ∑ x∈range r,dollar s^(a+1+x)*F (a+1+x)= g^a*W:=by
       unfold W; rw [mul_sum]; refine sum_congr rfl (fun i _=>?_); rw [show a+1+i=a+(i+1) by omega]; change g^(a+ (i+1))*_=_; rw [pow_add, mul_assoc]
    let y:= P.expect g (sing w g*f g)-∑ i∈range (a+1),g^i*F i
    rw [← sub_sub]; change g⁻¹^a*y=g⁻¹^a*(y-A)+W; unfold A; rw [show ∑ x∈range r,g^(a+1+x)*F (a+1+x) = _ from hz]; rw [inv_pow]; field_simp; ring

lemma inflates (hc:0 ≤ u)(hb:w.length ≤ d)(hy:Visit U X)(hR:Raw P U r (a+r+d) u) {i:ℕ}(hi:i<r):
     U.Ticket (r+1) (2^i*(u*(presence ψ X.Q (a+1+i))))
        (fun s=> dollar s^(i+1)*P.expect (dollar s) ((sing w *tale p ψ (a+1+i)) (dollar s))) := by
    let j:=a+1+i; let p' := (sing w*tale p ψ j); let C:=presence ψ X.Q j
    have he: Offers (a+r+d) C p':=by
       have h := ((Offers.words w hb).mul (hp.uses H.prices j)).widen (show d+j≤ a+r+d by unfold j; omega); rw [one_mul] at h; exact h
    let A x:= P.expect (dollar x) (p' (dollar x))
    have hA: U.Ticket r (u*C) A:= he.stints H p' rfl hy hc hR
    have h:= (hA.engage (i+1)).reduce (show r+1≤r+(i+1) by omega); rw [show _-(r+1)=i from ?_] at h; exact h
    omega
end ticket

variable (Y:Good X) (ψ:I → (L→G.Color)→ℝ) (hψ:∀i,ContDiffAt ℝ ∞ (ψ i) 0)
include Y hψ
set_option maxHeartbeats 500000
-- Run `Estimator` BEFORE point data. Budget `Visit U` ensures odd signs, needed even when
-- measuring at different actual periods. No Gram addresses consumed here.
theorem accrue (r a N d:ℕ)(hc:0≤C)(hu:0≤u)(B:Stage) : ∃ (U:Stage)(v:ℝ), U.Above B ∧ Visit U X ∧ 0≤v ∧ ∀(ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(n:Side)(P:Planet X n ι k T) (_hP:P.Steady)
    (_:Raw P B r (a+r+d) u),(∀ i f p,Visible X (ψ i) f p N C→∀ w:Rail G ι,w.length≤d→ U.Ticket (r+1) v (lapse P a p (ψ i) f w)):= by
    let R := r+1+a
    choose E hE H using fun i=>Error.motion Y (ψ i) (hψ i) R d N C hc
    let q:=4*(R+d)
    obtain ⟨U,hB,hL,h⟩:= clean B q ((eventually_all.mpr H).and (willing Y))
    have hy : Visit U X:= fun x hx=>(h x hx).2
    let W i (j:ℕ):=2^j*(u*(presence (ψ i) X.Q (a+1+j))); let v (i:I):= E i+∑ j∈range r,W i j
    have hv (i:I):0≤v i:=add_nonneg (hE i) (sum_nonneg fun j _=> by unfold W presence; have := Y.thick.1; positivity)
    refine ⟨U,∑ i,v i,hB,hy,sum_nonneg (fun i _=>hv i),fun ι k T _ _ _ n P H hP i f p hf w hw=> ?_⟩
    let F x:= (dollar x)⁻¹^a * P.expect (dollar x) (sing w (dollar x)*Error R f (ψ i) p (dollar x)); let u j x:=dollar x^(j+1)* P.expect (dollar x) ((sing w*tale p (ψ i) (a+1+j)) (dollar x))
    have hF: U.Ticket (r+1) (E i) F:=by
        refine U.free (r+1) _ (hE i) _ ?_; intro x hx; let g:=dollar x; have hp := (h x hx).1 i n ι k T _ _ _ P H f p hf w hw; have hg:0<g:=dollar_pos _; unfold F; change |g⁻¹^a* _|≤_; rw [abs_mul,abs_of_nonneg (by positivity : 0≤g⁻¹^a)]; refine (mul_le_mul_of_nonneg_left hp (by positivity : 0≤g⁻¹^a)).trans ?_; unfold rate; change _*(x^q*g^R* _) ≤ x^_*g^(r+1)*_
        rw [show g⁻¹^a*(x^q*g^R* E i)= x^q*g^(r+1)*E i from ?_]; swap; unfold R; rw [pow_add]; rw [inv_pow]; field_simp
        gcongr; exact hE i; exact U.high.trans hx
    have hh:=hF.more (U.ticket_sum (r+1) (range r) u (W i) (fun j hj=> inflates H hf hu hw hy (Raw.broaden hP hB (le_refl _) (le_refl _)) (mem_range.mp hj)))
    refine (hh.promote (single_le_sum (fun i _=> hv i) (mem_univ i))).reload ?_; intro s hs; exact (joinedL H hf (hy s hs) (a:=a) (r:=r)).symm
end YM.RGComparison.Core16.Lumen
