import YM.FVAAlt2.Rocket.Licenses
/-! # On this very schedule, carry both formal cost application & lattice geometry
- physical mesh k, arbitrary from family (terminal truncated at 0). spacing in `ε` units
  relative to measuring step, periodized properties.S.Ice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge.Contract
open Function Set Filter MeasureTheory Topology Real Finset Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Taping Atlas
open PhysicalNext.Repeat.Legato Family Run
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X:Type} {G:Gauge}{K:KernelChoices} (Y:Oracle.Program K)(Z:∀ Q:Patch,Q.Branches K G)(C:Run G)(T:Contract C Y Z)
variable (stamp:X→ℕ)(H:∀ x,T.floor Y Z C ≤ stamp x)
set_option quotPrecheck false
local notation "B"=> T.profile Y Z C stamp H
local notation "L"=> C.family.path.levels
local notation "L'"=> C.family.S
local notation "W"=> T.atLevel Y Z C stamp H
local notation "u'"=>T.ceiling Y Z C stamp H
lemma actual_sizes (v:Page (T.profile Y Z C stamp H).entire): (B).depth v= (L').a (W v) / (L').a (u' v.bindW):=by
    let U (j):= (L').a j
    apply Page.proves (g:=fun v=>_) _ _ v -- change motive.E!
    · intro x; change (B).desk.l _= _; rw [( B ).opens]; change 1= U (_-0)/ U _; rw [Nat.sub_zero, div_self]; exact ( show 0<U _ from ( L' ).a_pos _ ).ne'
    intro w hw; let i:= W w.next; let j:= W w.prev; let p:= (B).L w.volW; have he:j=i+1:= T.vert_j Y Z C stamp H w -- patch=L T actual.
    have hP:p=(L').block i:= congr_arg Patch.L ( T.paid_level Y Z C stamp H w 0 |>.1 )
    rw [ Track.moved, hw, show (L').a (W w.prev)=(L').a (i+1) from congr_arg _ he, (L').a_step ]; unfold i at *; change (_ / ↑(( L' ).block _).val / _ ) * (p.val:ℝ)= _; rw [hP]; field_simp; rfl -- or ring
lemma at_bound (w:Page (T.profile Y Z C stamp H).entire): W w≤u' w.bindW:= Nat.sub_le ..
private lemma room (x:X): (B).batch x≤ (B).entire x:=by set m:=( B ).batch x; have hm:m ≥ 1 := ( B ).life x; change m≤ 2*(m*m); nlinarith
-- measuring index.K
abbrev meas (x:X):= W (⟨x,(B).batch x, T.room Y Z C stamp H x⟩:Page (B).entire)
lemma spacing (x:X):Real.exp (-(B).Θ x)= (L').a (u' x)/(L').a (T.meas Y Z C stamp H x):=by
    let v:Page (B).entire:= ⟨ x,(B).batch x,T.room _ _ C _ _ x⟩; rw [ ← inv_div, exp_neg ]; congr 1; rw [show exp _=_ from ((B).exp_th x),show _ ^ _=(B).depth v from rfl,(T.actual_sizes Y Z C stamp H v)]
-- terminal actual also far from t(? k_j). Affords every p-numeric, cutoff not chosen after.
lemma cofinal {l:Filter X}(h:Tendsto stamp l atTop): Tendsto (fun x=>T.atLevel Y Z C stamp H (Page.finallyW (B).entire x)) l atTop:=by
    have hh(x:X): (L).clock.J (T.atLevel Y Z C stamp H (Page.finallyW (B).entire x))=stamp x:=by
       let k:= u' x; let ζ:= (B).entire x
       have hk: ζ≤ k := T.has_space Y Z C (stamp x) (H _)
       exact T.enrol _ _ C (stamp x) (H x) (j:=k-ζ) (show k-ζ≤k-ζ from le_rfl) (show k-ζ≤k+ζ from by omega)
    refine tendsto_atTop.mpr (fun i=>?_); have hp:= (L).fits.mono; filter_upwards [h.eventually (eventually_gt_atTop (( L ).clock.J i))] with x hx; rw [← hh] at hx; exact ( hp.reflect_lt hx ).le -- check
end YM.RegulatorIR.FVAAlt2.Lodge.Contract
