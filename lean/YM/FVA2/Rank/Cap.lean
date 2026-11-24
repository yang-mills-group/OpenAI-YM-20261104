import YM.FVA2.Rank.Team
/-!
# Rank parity passes through native bulk SAT

At all scales, on any direction (not only net-zero). Prove directly via induction on finite capacity
of arbitrary solution. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue.Agent
open Function Filter Set Finset Lattice MeasureTheory Real
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Native MS.Native.Wilsonian MS.Book MS.Book.Program MS.Book.Convolve
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Menus MS.City
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{k i n m:ℕ}{p:Team}{r:ℤ}
variable (y:ℝ) (h: Wage k p) {A:Law G}{F H:Wind.Flow G}
lemma BP (a b: Law G) (h: Hue.only n a) (he: Hue.only m b)(t:ℝ) : Hue.only (n+m) ( boulevard parity (Cpu G t) a b ):= by
 rw [test_p] at *; -- use pilot
 rw [← black (p:=parity)]; rw [blvd, Pilot.Transport.gatherR (port _) _ _ ( X_even G t ) ( X_even G t ) ]; change Flux.tree parity _ _ _= _; rw [ black, black, h,he,← blvd, map_smul, map_smul,LinearMap.smul_apply,smul_smul,Hue.sp,mul_comm, blvd]
lemma stationary (h:TouchF F)(he:Rank F r)(ht:Sat A F H)(hH:∀ t,Hue.only i (H t))(hA:Hue.only i A)(t:ℝ): Hue.only i ( F t ):= by
 let m:=r.toNat+1; have hv : ∀ j≤ m, ∀ w:List (Lane4 G), i%2≠ w.length%2 → w.length≥j→∀ s:ℝ,F s w=0:= by
    intro j hj; induction hj using Nat.decreasingInduction with
    | self=> exact fun w _ hv t=> he t w (by unfold m at hv; omega)
    | of_succ j hj ih=>
        intro w hw hz u; rw [ ← ht.1 ] at hA; refine Eq.trans ?_ (hA w hw); apply Wind.constancy (f:=fun x:ℝ=> F x w); intro s
        convert! ht.2 s w using 1; rw [ Pi.add_apply, hH s w hw,add_zero ]; change 0= Heat.orbit (Cpu G s) μzone (F s) w; rw [ finite_cc μzone (period0 μzone cour0 (main_f _) h) ]; unfold Ccy; have hj(x:QP): Flux.trc (Cpu G s) x (F s) w=0:= by
            rw [ Flux.at_trc ]; refine Finset.sum_eq_zero fun u _=> Finset.sum_eq_zero fun v _=>?_ ; rw [ih _ (by simp; omega) (by simp; omega) s, mul_zero]
        simp_rw [hj]; simp
 exact fun w hw=> hv 0 ( Nat.zero_le _ ) w hw ( Nat.zero_le _ ) _
variable {X:Dec G}
include h
lemma nav (he: PC G p X)(hi:i≤k)(t y:ℝ): Hue.only i ( X i y t ):= by
    induction i using Nat.strong_induction_on generalizing t with
    | h i ih =>
        by_cases hx:i=0; · subst i; rw [he.free]; exact fun _ _=>rfl
        obtain ⟨r,hr⟩:= (he.owes i).pay; refine stationary ((he.owes i).stay y|>.joint) (hr y) ( he.recu i ( Nat.pos_of_ne_zero hx ) y ) ?_ ( first_p y h i hi G ) _; intro u w hw; simp only [ Wind.path, Finset.sum_apply, Pi.smul_apply ]; rw [Finset.sum_eq_zero (fun n hn=>?_ ), smul_zero]; obtain hp:= path_in hn; obtain ht:= BP ( X (i-n) y u ) ( X n y u ) (ih (i-n) (by omega) (by omega) u) (ih n (by omega) (by omega) u) u; exact ht w (by omega)
theorem TrueSky (G:Gauge)(hi:i≤k)(w:ℝ×ℝ): Hue.only i ( col ( skyline G p ) i w):= nav h (skyPC G p) hi _ _
end YM.FVA2.Hue.Agent
