import YM.FVA2.XReg.Choice
/-!
# Move reports into X coupling without errors amplified

Use triangular charging at any $i$, through all orders (finite restriction). No assumed parity
or even alignment. CoreR argument. Construct $f(t)=t+O(t²)$ as all-orders inverse.
Keep its API explicit rooted, left & right inverses, orientation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Token
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open Normalize.Fray Reg.Point Reg.Unique Pivot CoverTest Higher State Choice
open scoped Topology ContDiff BigOperators Classical
variable {n d k:ℕ}{G:Gauge}
local notation "Π"=> Press.portDeck G
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
section formalClock
variable {L N:Cn}
structure Payment (t x:Cn): Prop where
    launch : Rooted t
    own : Rooted x
    left : x.subst t=X
    right : t.subst x=X
variable (t:Cn)
abbrev back (t:Cn) : Cn:= if h:coeff 1 t=1 then t.substInvOfIsUnit ( by rw [h]; exact isUnit_one ) else X
lemma covers (h:Rooted t)(ht:coeff 1 t=1): Payment t (back t):= by have h0: constantCoeff t=0:= ( coeff_zero_eq_constantCoeff_apply _ ).symm.trans h; unfold back; rw [dif_pos ht]; refine ⟨ h, cert (by rw [constantCoeff_substInvOfIsUnit]), subst_substInvOfIsUnit_left t h0 _, subst_substInvOfIsUnit_right t h0 _⟩
lemma stamp_t (h:Rooted t)(ht:coeff 1 t=1): coeff 1 (back t)=1:= by obtain hx:= coeff_one_X (R:=ℂ); rw [← (covers t h ht).left, stating_one _ _ h, ht,mul_one] at hx; exact hx
lemma paid {K:Cn}(h:Payment t N) (hp:N.subst K=X)(hv:Rooted K) : K=t:= by
    have hx: PowerSeries.subst K (t.subst N)=(t:Cn):= (by rw [subst_comp_subst_apply (licence N h.own) (licence K hv), hp, X_subst]); rw [h.right, subst_X (licence K hv)] at hx; exact hx
lemma both (h:Payment L N) : Payment N L:= ⟨h.own,h.launch,h.right,h.left⟩
lemma core_l {q:Cn}(H:Payment t q) (h:CoreR t): CoreR q:= by
    let p:=PowerSeries.map (starRingEnd ℂ) q
    have hp : Rooted p:= by unfold p Rooted; rw [ coeff_map,H.own,map_zero ];
    apply paid q (both H) ( K:=PowerSeries.map (starRingEnd ℂ) q ) _ hp -- argument `paid q`, wants t=q and N=t.F.Back.right
    nth_rw 1 [ ← h ]; rw [← FPS.substitute_ringHom (starRingEnd ℂ) t ?_, H.right ]; · simp
    exact (coeff_zero_eq_constantCoeff_apply _).symm.trans H.own
end formalClock
section harmony
variable {I:Type*}{P:Filter I}{L q:Cn}{Q:I→ Cn}
lemma law (i:ℕ) (h: Harmony P Q q) : Harmony P (fun a=> Q a ^ i) (q^i):= by induction i with | zero=> simp only [pow_zero]; exact fun _=> tendsto_const_nhds | succ i ih=> simp only [pow_succ]; exact Harmony.mul ih h
lemma stamp_n (p:Cn)(h:Rooted p)(m:ℕ): coeff m (p^m)=(coeff 1 p)^m:= by
    induction m with
    | zero=> simp
    | succ i ih=> rw [pow_succ, pow_succ,coeff_mul, Finset.sum_eq_single (i,1) ]; rw [ ih ] -- names
                  · intro x hx hv; obtain hh:=Finset.mem_antidiagonal.mp hx; by_cases he:x.2=0; rw [he,h,mul_zero]; have ht:x.1< i:= by contrapose! hv; exact Prod.ext (by dsimp; omega) (by dsimp; omega)
                    rw [show coeff x.1 (p^i)=0 from Program.blocked h ht,zero_mul]
                  simp
abbrev tend (p q:Cn)(m:ℕ): ℂ:=∑ i∈Finset.range m, coeff i p * coeff m (q^i)
lemma meter (p:Cn)(h:Rooted q) (m:ℕ)(hq:coeff m (q^m)≠0): coeff m p=( coeff m (p.subst q) - Token.tend p q m)/ coeff m (q^m):= by rw [eq_div_iff hq,FPS.coeff_substituted _ ((coeff_zero_eq_constantCoeff_apply _).symm.trans h), Finset.sum_range_succ, Token.tend]; rw [smul_eq_mul]; rw [show ∑ i∈Finset.range m,coeff i p * coeff m (q^i)= ∑ i∈Finset.range m,coeff i p • coeff m (q^i) from rfl]; abel
lemma earn (p:I→ Cn) (R:Cn)(h:Rooted q)(hs:coeff 1 q≠0)(hr:∀ᶠ i in P,Rooted (Q i))(hq: Harmony P Q q)(hk: Harmony P (fun i=> (p i).subst ( Q i )) ( R.subst q )): Harmony P p R:= by
    intro m; induction m using Nat.strong_induction_on with
    | h m ih=>
       have ht:= law m hq; have hM: coeff m (q^m)≠0:= by rw [stamp_n _ h]; exact pow_ne_zero _ hs
       rw [meter R h m hM]; have he : Tendsto ( fun i=> Token.tend (p i) (Q i) m ) P (𝓝 ( Token.tend R q m )):= tendsto_finsetSum _ (fun i hi=> (ih i (Finset.mem_range.mp hi)).mul ( law i hq m ))
       apply (((hk m).sub he).div ( ht m ) hM ).congr'; filter_upwards [hr, (ht m).eventually ( eventually_ne_nhds hM )] with i hu hv; exact Eq.symm ( meter ( p i ) hu m hv )
end harmony
open Pivot State Higher
variable (ν:ℝ){V:Normalize.Store G}(K:Rose.Pick V){O:Booked (Press.portDeck G)} (T: MS_Data G O)
def conversion := back (choice ν K T)
local notation "ρ"=> conversion ν K T
-- ClockToken.Stress.
variable (h:G.Simple)
abbrev leaf_t (d:ℕ): Guard G d:= stepV (conversion ν K T) (chooseL ν V T d)
-- For the actual use see `Faith`. No claim about any changes to the MS
-- dimensional or book conventions.
end YM.FVA2.Reg.Token
