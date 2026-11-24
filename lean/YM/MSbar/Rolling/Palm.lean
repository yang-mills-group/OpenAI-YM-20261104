import YM.MSbar.Pulse.Spot
/-!
# A Wilson native Feynman step

We prove statements over _finite_ tori first. In this module a statement
about a formal series may be earned by ordinary Laplace asymptotics in
fixed finite dimension, including its Ward identities (from an invariant
denominator, not imposing an invariant germ by hand). Nothing about the
sizes of the constants in Palm is to be used as a cutoff-independent
error bar. In particular, evaluation of the constructed History, with
shoots set by the bar and levels in their increasing β schedule, is NOT
an application of an unquantified `Eventually` with inputs or periods
varying. We need the expansion *formula* as well as the tail bills which
will make it valid at large cuts. Logs below are real.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Function Filter MeasureTheory Set Asymptotics Cacao
open scoped Topology Classical BigOperators
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
-- costs as g→0 with polynomial in ℓ = log(g^-1)
def fuel(x:ℝ):= Real.log x⁻¹
lemma awake : Tendsto fuel Γ atTop:= Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
lemma width : ∀ᶠ x:ℝ in Γ,0<x ∧ x≤1∧1≤fuel x :=(show ∀ᶠ x:ℝ in Γ,0<x from self_mem_nhdsWithin).and (((eventually_lt_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds |>.mono (fun _ h=>h.le))|>.and (awake.eventually_ge_atTop 1))
lemma subs (n:ℕ) : Tendsto (fun x:ℝ=> x*fuel x ^ n) Γ (𝓝 0):=by
    refine ((Real.isLittleO_pow_log_id_atTop (n:=n)).tendsto_div_nhds_zero.comp tendsto_inv_nhdsGT_zero).congr (fun i=> ?_); change _/i⁻¹=_; simp [fuel,id]; ring
-- Absorb fixed constants into an extra log.
variable {σ E F : Type*} [SeminormedAddCommGroup E][SeminormedAddCommGroup F]
variable {X Y:ℝ→σ→Prop} {p q:ℕ} {f g:ℝ→σ→ E}
def Price (X:ℝ→σ→Prop)(p:ℕ)(f:ℝ→σ→E): Prop :=∃ N:ℕ,∀ᶠ x in nhdsWithin 0 (Set.Ioi 0),∀ y:σ,X x y→ ‖f x y‖ ≤ x^p * fuel x ^ N
namespace Price
lemma fixed (N:ℕ)(K:ℝ)(h:∀ᶠ x:ℝ in Γ,∀ y:σ, X x y→ ‖f x y‖ ≤ K*(x^p*fuel x^N)) : Price X p f:=by
    refine ⟨N+1,?_⟩; filter_upwards [width,h,awake.eventually_ge_atTop K] with x ⟨hx,hh,he⟩ hh' hk; intro y hy; refine (hh' y hy).trans ((mul_le_mul_of_nonneg_right hk (by positivity : 0≤ x^p*fuel x^N)).trans_eq ?_); ring
lemma reach (h:Price X p f) (A:ℝ)(hx:0<A)(hp:0<p): ∀ᶠ x in Γ,∀ y, X x y→ ‖f x y‖ < A:=by
    obtain ⟨K,hK⟩:=h; filter_upwards [width,hK,(subs K).eventually (eventually_lt_nhds hx)] with x ⟨hx',he,hf⟩ hs hg; intro y hy; exact (hs y hy).trans_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_of_le_one hx'.le he (show 1 ≤ p from hp)) (pow_nonneg (zero_le_one.trans hf) K)) hg)
lemma bounds (hq:Price X p f)(q:∀ᶠ x in Γ,∀ y, X x y→ ‖g x y‖ ≤ ‖f x y‖):Price X p g:=by
    obtain ⟨N,hp⟩:=hq; refine ⟨N,?_⟩; filter_upwards [q,hp] with x hv h y hy using (hv y hy).trans (h y hy)
lemma egress (hq:Price X p f)(q:∀ᶠ x in Γ,∀ y, X x y→ f x y=g x y):Price X p g:=hq.bounds (q.mono fun x a y h=> (le_of_eq (congr_arg _ (a y h)).symm))
lemma weaken (h:Price X p f)(q:∀ᶠ x in Γ,∀ y, Y x y→ X x y):Price Y p f:=by
    obtain ⟨N,hp⟩:=h; refine ⟨N,hp.mp ?_⟩; filter_upwards [q] with x hv h y hy using h y (hv y hy)
lemma poorly (h:Price X p f)(hp:q≤p):Price X q f:=by
    obtain ⟨N,h⟩:=h; refine ⟨N,?_⟩; filter_upwards [h,width] with x h ⟨hx,he,hf⟩; exact fun y hy=> (h y hy).trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hx.le he hp) (by positivity))
lemma top (h:Price X p f)(q:∀ᶠ x in Γ,∀ y, Y x y→ X x y):Price Y 0 f:= (h.weaken q).poorly (Nat.zero_le _)
lemma fromConst (x:E) : Price X 0 (fun _ _=> x) := fixed 0 ‖x‖ (Eventually.of_forall (fun x y hy=> by simp))
lemma nil : Price X p (fun _ _=>(0:E)):=⟨0,width.mono fun x hx y _=>by rw [norm_zero,pow_zero,mul_one]; exact pow_nonneg hx.1.le _⟩
lemma nsum (h:Price X p f) (k:Price X p g):Price X p (fun x y=> f x y +g x y):=by
    obtain ⟨n,he⟩:=h; obtain ⟨m,hi⟩:=k; refine fixed (max n m) 2 ?_; filter_upwards [width,he,hi] with x ⟨hf,h0,hv⟩ ht hK y hy; apply (norm_add_le ..).trans <| (add_le_add (ht y hy) (hK y hy)).trans ?_; rw [two_mul]; gcongr <;> first| exact le_max_left ..| exact le_max_right ..
lemma neg (hq:Price X p f) : Price X p (fun x y=> -(f x y)) := hq.bounds (Eventually.of_forall (fun x y _=> (norm_neg _).le))
lemma cut (hq:Price X p f)(q:Price X p g) : Price X p (fun x y=> f x y-g x y):= (hq.nsum q.neg).egress (Eventually.of_forall fun x y _=> (sub_eq_add_neg ..).symm) -- align
lemma val [NormedSpace ℝ E] {w:ℝ→σ→ℝ} (h:Price X p w)(k:Price X q f):Price X (p+q) (fun x y=> w x y • f x y):=by
    obtain ⟨n,he⟩:=h; obtain ⟨m,hi⟩:=k; refine ⟨n+m,?_⟩; filter_upwards [width,he,hi] with x ⟨h0,h1,hx⟩ hg hA y hy; rw [norm_smul]; refine (mul_le_mul (hg y hy) (hA y hy) (norm_nonneg _) (by positivity)).trans_eq ?_; ring
lemma product {g h :ℝ→σ→ℝ} (x:Price X p g)(z:Price X q h):Price X (p+q) (fun y i=>g y i*h y i):= val x z
lemma pow {g:ℝ→σ→ℝ}(h:Price X p g)(q:ℕ) : Price X (p*q) (fun y i=>g y i^q):=by
    induction q with
    | zero=> simpa only [Nat.mul_zero,pow_zero] using (show Price X 0 (fun y i=>g y i^(0:ℕ)) from (fromConst (1:ℝ)).egress (Eventually.of_forall fun _ _ _=>(pow_zero _).symm))
    | succ i ih=> rw [Nat.mul_succ]; exact (product ih h).egress (Eventually.of_forall fun x y _=> (pow_succ ..).symm)
lemma xunit (X:ℝ→σ→Prop): Price X 1 (fun x y=>x):=⟨0,width.mono (fun x hx y _=> by simp [Real.norm_eq_abs,abs_of_pos hx.1])⟩
lemma xrise (X:ℝ→σ→Prop) (n:ℕ): Price X n (fun x y=> x^n):=by simpa only [one_mul] using ((xunit X).pow n)
lemma bag {A:Type*}(I:Finset A)(g:A→ℝ→σ→E)(h:∀ a∈I,Price X p (g a)): Price X p (fun x y=>∑ a∈I,g a x y):=by
    classical
    induction I using Finset.induction with
    | empty=>simpa using (nil : Price X p (fun _ _=>(0:E)))
    | insert i I he ih=> simpa only [Finset.sum_insert he] using ((h i (Finset.mem_insert_self ..)).nsum (ih fun a ha=>h a (Finset.mem_insert_of_mem ha))) -- target simplifies but using tactic
omit [SeminormedAddCommGroup F] in
lemma inherits {V:ℝ→F→Prop}(r:Price X p f) (z:ℝ→F→σ)(hv:∀ᶠ x in Γ,∀ y,V x y→ X x (z x y)):Price V p (fun x y=>f x (z x y)):=by
    obtain ⟨t,hi⟩:=r; refine ⟨t,hi.mp ?_⟩; filter_upwards [hv] with x hv he y hy using he _ (hv y hy)
end Price
end YM.MSbar.Rolling
