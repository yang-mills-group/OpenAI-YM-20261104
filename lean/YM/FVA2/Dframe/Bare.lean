import YM.FVA2.Dframe.Gram
import Mathlib.Analysis.Polynomial.Basic
/-!
# The leading matrix equals the identity at finite mesh

This will be essential in identifying the position frames (see `XReg/Post` and
`XReg/Unique`). This identity concerns the *order-zero matrix*. We don't say
that the matrix itself converges in higher orders!

Sketch of argument. Fix a column X ($g$ below indexes its `Plaid` label, at its
own dimension d). Initial allowed form: can strictly lower slot rank here, (`prime`
for identity action in the other entries). Induct on slot rank (`Toon.grade` -- NOT
the engineering dimension). If already exact identity on all lower ranks, test the
column of the order-zero matrix against the Gram array at the specified reflected
point, using the lower-rank fields. Use both leading convergences (before and after D),
and *exact* known action on those lower ranks. Then after subtracting the identity
component of the column, the tested difference tends to zero. Identify it as the linear
action of the finite-regulator Gram on just that column of possibly nonidentity entries,
use nonsingularity **of the limiting Gram** and convergence to conclude those entries all
tend to zero as well (`paid_m`). Now because of the scale factors and actual polynomial
log-fees used in these entries, this is only possible if the fees were literally zero
(`isBorn`)!

No positivity assumption on the finite-regulator theory. See `Dframe/Gram` for `Sec`
free Gram; see `Main.Match.D_initial` for the application to the actual data. For this
comparison `TaylorOKF` from the `Inked`/`Full` construction (so the `tB` invoked is
for the correct `S` on the actual posted array).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Dframe.Silver
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
variable {n d k:ℕ}{G:Gauge}{B:Deck G}
variable (ν:ℝ) (Y:XSpace.Initialize G) (S:Prescription (Press.portDeck G))
local notation "Π"=> Press.portDeck G
variable (a: Sample n) (t:Tags G d n) (m:Mesh) (g:Plaid (Press.portDeck G) d)
abbrev high (d:ℕ)(a:Mesh) := wold ν S a d 0
lemma status_lead (R:Guard G d) (V:ℕ→Point G d n) : status R V 0 t= V 0 (fun i=> coeff 0 R (t i)):= by rw [seen,tally,Finset.finsuppAntidiag_zero, Finset.sum_singleton]; rfl
lemma stillT : postedPoint ν Y S d a 0 t= live Y d a 0 ((high ν S d a.F ) ∘ t) := by unfold postedPoint; rw [ status_lead,orderT,pay0,pays ]; rfl
local notation "X"=> Land.read g
abbrev Poor (g:Plaid (Press.portDeck G) d):= {x:Toon G d // x.grade<(Land.read g).grade}
local notation "F"=> Poor g
abbrev owed (m:Mesh)(u: Poor g): ℂ := (stake ν S m X u.val 0:ℝ)
lemma h_lit : high ν S d m (theory X)=∑ x:Toon G d, ((stake ν S m X x 0:ℝ):ℂ) • theory x:= by
    rw [high,w_lit]; change (∑ i:Toon G d,stake ν S m X i 0 • theory i)= _; exact Finset.sum_congr rfl fun i _=> (IsScalarTower.algebraMap_smul ℂ ( stake ν S m X i 0 ) (theory i ) ).symm
lemma rankOK (i:Toon G d)(h:(X).grade ≤ i.grade): (( S.fees d g 0 ).register i)= if i=X then 1 else 0:= (S.init d g).Single i h
lemma prime (i: Toon G d) (h:(X).grade ≤ i.grade): (stake ν S m X i 0)= if i=X then 1 else 0:= by
    change m.spacing⁻¹ ^ (d-i.size) * ((S.fees d g 0).register i).eval _= _; rw [rankOK S _ i h]; split_ifs with ht; · subst i; rw [show (X).size=d from rfl]; simp
    simp
lemma basis : LinearIndependent ℂ (fun i: Poor g=> theory i.val):= by simp_rw [ ← theory_sig ]; exact (Theater.Daylight Π d ).linearIndependent.comp _ Subtype.val_injective
lemma falls : Gram.Join (fun i: Poor g=> theory i.val) ( owed ν S g m )= high ν S d m (theory X) - theory X := by
    rw [eq_sub_iff_add_eq,h_lit]; let s := Finset.univ.filter fun i:Toon G d=> i.grade<(X).grade; let F'(i:Toon G d):= (↑(stake ν S m X i 0):ℂ) • theory i;
    change (∑ i:Poor g,F' i.val) + _=∑ i,F' i; rw [← Finset.sum_subtype s ( show ∀ i: Toon G d,i∈s↔ i.grade < (X).grade from fun _=> by simp [s] ) F', ← Finset.sum_filter_add_sum_filter_not (s:=Finset.univ) (p:=fun i: Toon G d=> i.grade<(X).grade) ]; congr 1; -- tactic
    rw [ Finset.sum_eq_single_of_mem X ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, not_lt_of_ge ( le_refl (X).grade ) ⟩ ) ]; · unfold F'; rw [prime _ _ _ _ _ (le_refl _),if_pos rfl,Complex.ofReal_one,one_smul];
    intro i h hi; unfold F'; rw [prime _ _ _ _ _ (le_of_not_gt ( Finset.mem_filter.mp h|>.2 )), if_neg hi,Complex.ofReal_zero, zero_smul]
local notation "H"=> high ν S
abbrev Success (g:Plaid (Press.portDeck G) d) := ∀ i: Toon G d, (( S.fees d g 0 ).register i)= if i=Land.read g then 1 else 0
lemma exact_at (c:Toon G d)(he:Success S (panel c)): high ν S d m (theory c)=theory c:= by
 let v:= Land.read (panel c); let H0:= theory c; have hc: high ν S c.size m (theory v)=theory v:= by
    rw [h_lit ν S m (panel c) ]; rw [Finset.sum_eq_single v];
    · rw [prime _ _ _ _ _ (le_refl v.grade),if_pos rfl,Complex.ofReal_one,one_smul];
    · intro i _ hi; unfold stake ink; change (↑(m.spacing⁻¹^ ( v.size-i.size ) * ((S.fees c.size (panel c) 0).register i).eval _) :ℂ) • theory i=0; rw [ he i, if_neg hi ]; simp
    simp
 change H d m H0= _; rw [show H0= (up (size_le c)) (theory v) from rfl, show H d m (( up (size_le c)) (theory v))= (up (size_le c)) ( H c.size m (theory v) ) from coast ν S m _ (size_le c),hc]; rfl
lemma history_p {I:Type*}{V:Filter I} [V.NeBot] (R:Polynomial ℝ) (t:I→ℝ)(h:Tendsto t V atBot)(he:Tendsto ( fun i=> R.eval (t i) ) V (𝓝 0)): R=0:= by
    by_cases hp:0<R.degree
    · obtain hh:Tendsto (fun i=>|R.eval (t i)|) V (𝓝 |(0:ℝ)|):= continuous_abs.continuousAt.tendsto.comp he; obtain h':= (( Polynomial.abs_tendsto_atBot R hp ).comp h).eventually ( eventually_gt_atTop 1 ); obtain ⟨i,hi,h⟩:= (hh.eventually ( gt_mem_nhds ( show |(0:ℝ)|<1 from (by norm_num) ))|>.and h').exists; exact False.elim (lt_asymm (show |R.eval (t i)|<1 from hi) h )
    let x:= R.coeff 0; have hv : R=Polynomial.C x:= Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hp); have hx:Tendsto (fun _:I=>x) V (𝓝 0):= he.congr fun i=> (congr_arg (Polynomial.eval ( t i )) hv).trans Polynomial.eval_C; rw [ hv,tendsto_nhds_unique tendsto_const_nhds hx,map_zero]
open Gram
local notation "Y₀"=> (Sample 2)
local notation "i'"=> (0:Axis)
private abbrev w : E4:= WithLp.toLp 2 (fun _:Axis=>(1:ℝ))
local notation "ε"=> γ i' w
local notation "ℒ"=> Gate ε
private lemma δpos : 0< w i':= show (0:ℝ)<1 from zero_lt_one
private lemma γsafe : ε∈conf _:= γsep _ _ δpos
local notation "Ω"=> live Y d
lemma DuoSpin (a:Sample 2)(p q:Sec G d)(Hs:Favors.Horder S): Gram.cost i' ( postedPoint ν Y S d a 0 ) p q= Gram.cost i' (Ω a 0) ( H d a.F p) ( H d a.F q ):= by
    unfold Gram.cost; rw [ stillT ]; congr 1; funext i; fin_cases i; · change (wold ν S a.F d 0) (ori (Signed.mirror i').ortho _ ((Normalize.reel d) p))= (ori (Signed.mirror i').ortho d) (Normalize.reel d ((wold ν S a.F d 0) p)); rw [← w_yaw (G:=G) _ _ _ _ ( Signed.mirror i' ) Hs, w_reel ];
    rfl
variable {P:Booked (Press.portDeck G)}(T: MS_Data G P)(h:G.Simple)(hp:TaylorOKF T (Press.wickInput Y) S)(hq:Favors.Horder S)
include h hp hq

/-- The Gram argument for the possibly nonidentity entries. -/
lemma paid_m (IH:∀ z:Poor g, Success S (panel z.val)) :
        Tendsto (fun i:Y₀=> owed ν S g i.F ) (Gate ε) (𝓝 0):= by
 let e(i:Poor g):= theory i.val
 let K:=Normalize.scene ε d (G:=G)
 let R:=Gram.stage i' K e
 let v: Sec G d:= theory X
 let Dm(i:Y₀):= high ν S d i.F
 let Am(i:Y₀):=Gram.stage i' (live Y d i 0) e
 have he:= γsafe
 -- Unposted Gram converges to the positive definite one (on that subspace).
 have hh:Tendsto Am ℒ (𝓝 R):=
    Gram.walk _ _ _ _ (fun v=> notices Y d v ε he)
 apply Gram.wish (R:=R) _ (Gram.nonsing _ _ _ δpos (basis g)) hh
 -- Now test also *after* D action.
 apply tendsto_pi_nhds.mpr
 intro x
 let f:= e x
 have hv:= tB ν Y S T h hp 0 (duo i' f v) ε he
 simp only [limit_lead ν T he] at hv
 obtain hs:= hv.sub ( notices Y d (duo i' f v) ε he )
 rw [sub_self] at hs
 apply hs.congr
 intro i
 change Gram.cost i' _ f v - Gram.cost i' _ f v= (Gram.stage i' _ e *ᵥ _) x
 rw [ DuoSpin ν Y S i f v hq, show H d i.F f=f from exact_at _ _ _ x.val ( IH x ),
      account, show Join e ( owed ν S g i.F )=_ from falls ν S i.F g,
      costQ,costQ,costQ,map_sub ]

include ν
lemma isBorn (IH:∀ z:Poor g,Success S (panel z.val))(x:Poor g) :
        ( S.fees d g 0 ).register x.val=0:= by
    let η(i:Y₀):= ν- Schedule.theta i.F
    let L:= Gate ε
    let R:= ( S.fees d g 0 ).register x.val
    -- Go to large negative lattice log scale parameter at fixed ν.
    have hL:Tendsto η L atBot:= by
      apply tendsto_atBot.mpr
      intro b
      filter_upwards [(Schedule.speed ε).eventually (eventually_ge_atTop (ν-b))] with i hi
      unfold η; linarith
    apply history_p R η hL
    obtain hx : Tendsto (fun i:Y₀=> stake ν S i.F X x.val 0) L (𝓝 0):=
        Complex.continuous_re.continuousAt.tendsto.comp
          (tendsto_pi_nhds.mp ( paid_m ν Y S g T h hp hq IH ) x)
    -- Remove the explicit engineering (inverse power of spacing) factors.
    let k:=d-x.val.size
    obtain ht := hx.mul ((stepG ε).pow k)
    rw [zero_mul] at ht; apply ht.congr; intro i; have h0:= i.F.positive.ne'
    change i.F.spacing⁻¹ ^ k * R.eval (η i)*i.F.spacing^k=_
    rw [ inv_pow, mul_right_comm, inv_mul_cancel₀ (pow_ne_zero _ h0),one_mul ]
-- For proving `Success` it actually suffices to call at one arbitrary ν (log units).
-- NOT saying that argument applies if the fees could be something other than polynomials.
omit ν
lemma full : ∀ (d:ℕ) (g:Plaid Π d), Success S g:= by
    suffices hB: ∀ k d:ℕ,∀ g: Plaid Π d, (Land.read g).grade=k → Success S g from fun d g=> hB _ _ g rfl; intro k; induction k using Nat.strong_induction_on with
    | h k ih =>
        intro d g he z; by_cases ht:( Land.read g ).grade ≤ z.grade; · exact rankOK S g z ht
        have hu : z.grade<( Land.read g).grade:= Nat.lt_of_not_ge ht; rw [if_neg (fun h=> ( by rw [h] at hu; exact Nat.lt_irrefl _ hu )) ]; exact isBorn 0 Y S g T h hp hq (fun j=> ih j.val.grade ( he ▸ j.property ) _ _ rfl ) ⟨z,hu⟩
lemma εborn : Success S g:= full Y S T h hp hq d g
include ν
lemma permits : high ν S d m=1:= LinearMap.ext fun i=> by rw [← all_sig i,map_sum]; simp only [ Module.End.one_apply ]; apply Finset.sum_congr rfl; intro j _; rw [ _root_.map_smul,exact_at ν S m j ( εborn Y S _ T h hp hq )]
lemma dawn : PowerSeries.constantCoeff (D ν S m d)=1:= by rw [← coeff_zero_eq_constantCoeff_apply, pays]; exact permits ν Y S m T h hp hq
omit h hp hq in
lemma positive_form (k:ℕ) (h:k≠0) (hP:Favors.Horder S) (he: Ace.UnitP S) : PowerSeries.coeff k (D ν S m d) ∈ Normalize.Change G d:= by rw [ pays ]; exact ⟨ ( w_unit _ _ _ he ).trans (if_neg h), fun i hi p hx=> preserves ν S m p hi hx, fun p=> (w_reel ν S m p).symm, fun s p=> ( w_yaw ν S m p s hP ).symm ⟩
lemma formal_price (hs:Ace.UnitP S): Formal (D ν S m d):= by
    let t (i:ℕ): Normalize.Change G d:= if he:i=0 then 0 else ⟨PowerSeries.coeff i ( D ν S m d ),positive_form ν S m i he hq hs⟩; have hv:= dawn (d:=d) ν Y S m T h hp hq; constructor
    · refine ⟨ t, PowerSeries.ext fun i=> ?_⟩; by_cases hi:i=0; · subst i; rw [ coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,const_deck,hv, show t 0=0 from dif_pos rfl, stand0 ]
      rw [ pos_decked _ hi ]; change _=((if hj:i=0 then 0 else (⟨ PowerSeries.coeff i _,positive_form ν S m i hj hq hs⟩: Normalize.Change G d))).val; rw [ dif_neg hi ]
    apply (PowerSeries.isUnit_iff_constantCoeff (R:=FieldEnd G d) (φ:=D ν S m d)).mpr; rw [hv]; exact isUnit_one
end YM.FVA2.Dframe.Silver
