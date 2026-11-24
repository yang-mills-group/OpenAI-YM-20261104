import YM.FVA2.Lambda.Run
/-!
# Parity of MS coupling scale, and the leading nonlinearity slope

This is in the bare clock at all orders and the continuum physical readings
of our common prescription. No numerical coefficient in this module. We prove
an extraction of β slope from the actual $W$ prediction. Even powers in MS
coupling absent. Not yet re parity of physical field labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta
open Hue.Agent Hue.Agent.Kappa
namespace Pen
local notation "r" => (-PowerSeries.X:Cn)
-- Defining minimal clock; reflection through sources unaffected.
lemma zero : Rooted r:= by simp [Rooted]
lemma ink (p:Cn)(n:ℕ) : coeff n ( p.subst (-PowerSeries.X) ) = (-1)^n * coeff n p:= by
  rw [ ← Constants.actual_subst _ _ zero, coeff_mk, rules, Finset.sum_eq_single n ]
  · unfold Program.cut; rcases Nat.even_or_odd n with h|h
    · rw [h.neg_pow,h.neg_pow, coeff_X_pow]; simp
    · rw [h.neg_pow,h.neg_pow,map_neg,coeff_X_pow]; simp
  · intro b _ h; unfold Program.cut; rcases Nat.even_or_odd b with H|H <;> simp [H.neg_pow,h.symm, PowerSeries.coeff_X_pow]
  simp
lemma wipe (p:Cn)(h:p.subst r= -p)(n:ℕ)(ht:Even n): coeff n p=0:= by
  have hm:= ink p n; rw [h,map_neg,ht.neg_pow (1:ℂ),one_pow, one_mul] at hm; exact (neg_eq_self ..).mp hm
lemma shifted (p:Team)(x:ℝ)(h:Correct p): (Program.shift p x).subst r= -Program.shift p x:= by
  apply PowerSeries.ext; intro n; rw [ink,map_neg ]; rcases Nat.even_or_odd n with he|he; · rw [ show coeff n (Program.shift p x)=0 from shift_b x ( show Wage n p from fun i _=> h.tone i ) _ (le_refl _) ((by have hx:= Nat.even_iff.mp he; omega)) ]; simp
  rw [ he.neg_pow ]; simp
end Pen
namespace LowBound
open Hue.Agent.Kappa
variable {G:Gauge}(ν:ℝ)(Y:XSpace.Initialize G){V:XSpace.Normalize.Store G}(K:XSpace.Rose.Pick V){O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G)) (t:ℝ)(h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "χ" => Measure.chi K ν T
local notation "φ"=> Measure.f K ν T
local notation "γ" => Scale.GroupS.ψ K T ν
local notation "π" => Scale.GroupS.Ψ K T ν
local notation "σ" => Program.shift S.team
local notation "Θ" => (-PowerSeries.X:Cn)
local notation "B"=> Scale.Beta.beta
local notation "Q"=> true_m ν Y K T S h hs hr hu
include h hs hr hu
lemma unique_q (x:ℝ) : π t= (back (σ x)).subst (σ (x-t)):= by
  obtain ht:= Reg.Token.covers (σ x) ( share .. ) ( ann .. ); rw [ Time.scale ν Y K T S t h hs hr hu x, ← subst_comp_subst_apply ( licence (σ x) (share ..) ) ( licence _ (Q t).start ), ht.left, subst_X ( licence _ (Q t).start ) ]
lemma location_free (a:ℝ): Scale.GroupS.Ψ K T a t= π t:=( unique_q a Y K T S t h hs hr hu (0:ℝ) ).trans ( unique_q ν Y K T S t h hs hr hu (0:ℝ)).symm
lemma turns (x:ℝ): (π t).subst Θ= -(π t):= by
  let P:=π t; have hP:Rooted P:= (Q t).start; let S':=σ x
  obtain hh:= standardF h hs; have he:Rooted (P.subst Θ):= circle _ _ hP Pen.zero; have hf:Rooted (-P):= by rw [Rooted,map_neg,hP,neg_zero];
  have hp': PowerSeries.subst (P.subst Θ) S'=PowerSeries.subst (-P) S':= by
     obtain hr' := Time.scale ν Y K T S t h hs hr hu x
     have hh': -P=PowerSeries.subst P Θ:= by rw [ ← coe_substAlgHom (R:=ℂ) (licence _ hP), map_neg, coe_substAlgHom (licence _ hP), subst_X (licence _ hP) ]
     rw [hh', ← subst_comp_subst_apply ( licence P hP ) ( licence Θ Pen.zero ), ← subst_comp_subst_apply ( licence Θ Pen.zero ) ( licence P hP ), show PowerSeries.subst Θ S'= -S' from Pen.shifted _ _ hh, ← coe_substAlgHom (R:=ℂ) (licence _ hP), map_neg, coe_substAlgHom (licence _ hP), ← show (σ (x-t))=PowerSeries.subst P S' from hr', Pen.shifted _ _ hh ]
  obtain ht:= covers S' ( share .. ) ( ann .. )
  have hv:= congr_arg (fun a:Cn=> PowerSeries.subst a (back S') ) hp'; change PowerSeries.subst (PowerSeries.subst (P.subst Θ) S') (back S')= PowerSeries.subst (PowerSeries.subst (-P) S') (back S') at hv; rw [ ← subst_comp_subst_apply ( licence S' ht.launch ) ( licence _ he ), ← subst_comp_subst_apply ( licence S' ht.launch ) ( licence _ hf ), ht.left, subst_X (licence _ he),subst_X (licence _ hf) ] at hv; exact hv
lemma formal_t (k:ℕ)(he:Even k): coeff k (π t)=0:= Pen.wipe _ ( turns ν Y K T S t h hs hr hu (0:ℝ) ) _ he
lemma beta_parity (k:ℕ)(he:Even k): coeff k ( B π )=0:= by
  obtain hv:= Scale.Beta.origin π (Precise.fitM ν Y K T S h hs hr hu) k; simp_rw [ formal_t ν Y K T S _ h hs hr hu k he ] at hv; exact hv.unique (hasDerivAt_const ..)
-- slope
lemma affair (x:ℝ): (↑((S.team 3).coupling.eval (x-t)):ℂ)= ↑((S.team 3).coupling.eval x)+ coeff 3 ( π t ):= by
  let P:=π t; obtain ht:Tangent P:= Q t
  have he:= Engine.one_time (p:=P) (q:=PowerSeries.X) (k:=3) ht.start Tangent.unit.start ( by intro i hi; interval_cases i; exact ht.start.trans Tangent.unit.start.symm; exact ht.lead.trans Tangent.unit.lead.symm; rw [ show coeff 2 P=0 from formal_t ν Y K T S t h hs hr hu 2 (by decide),PowerSeries.coeff_X ]; simp ) ( σ x ) (by decide);
  rw [ X_subst, ← show (σ (x-t))=(σ x).subst P from Time.scale ν Y K T S t h hs hr hu x, ann, one_mul, coeff_X, if_neg (by decide),sub_zero ] at he
  conv at he=> lhs; unfold Program.shift; simp only [coeff_mk, if_neg (show ¬ (3:ℕ)=1 from by decide), if_neg (show ¬ (3:ℕ)=0 from by decide)]
  exact sub_eq_iff_eq_add'.mp he
-- t generator response fixed. formula relative negative time shift.
lemma pace3 (x:ℝ): -(↑((Polynomial.derivative (S.team 3).coupling).eval x):ℂ)= coeff 3 ( B π ):= by
  let q:=(S.team 3).coupling
  have hx:HasDerivAt (fun t:ℝ=> (↑(q.eval (x-t)):ℂ)) ( -(↑((Polynomial.derivative q).eval x):ℂ) ) 0:= by
    let f:=fun t:ℝ=> x-t; have he:HasDerivAt f (-1) 0:= by convert! ( hasDerivAt_id (x:=(0:ℝ))).const_sub x
    obtain ht:= Complex.ofRealCLM.hasFDerivAt (x:=q.eval (f 0))
    have hv:= (show HasDerivAt _ _ ( f 0 ) from ( by rw [show f 0=x from sub_zero x]; exact Polynomial.hasDerivAt q x));
    convert! ht.comp_hasDerivAt _ ( hv.comp (0:ℝ) he ) using 1; simp
  simp_rw [ show ∀ t:ℝ, (↑(q.eval (x-t)):ℂ)= _ from fun t=> affair ν Y K T S _ h hs hr hu x ] at hx
  exact hx.unique (( Scale.Beta.origin π ( Precise.fitM ν Y K T S h hs hr hu ) 3 ).const_add _)
end LowBound
end YM.FVA2.Lambda
