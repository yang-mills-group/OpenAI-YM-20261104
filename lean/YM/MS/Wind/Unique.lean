import YM.MS.Wind.Felt
/-!
# Uniqueness on any solution with rank capacity

Applied to both marks and near test. Tree terms become forcing. `f0` upper beyond target. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H P Q:Flow G}{A A':Law G}{b:Bool}{u v r:ℤ}{t:ℝ}
-- stationary rank test >=
structure Near (b:Bool)(F:Flow G): Prop where
   touch : TouchF F
   limit : ∃ r, Rank F r
   pays t (w:List (Lane4 G))(h:Course b w): HasDerivAt (fun t=> F t w) (Wiref G F t w) t
lemma constancy {f:ℝ→ℂ}(h:∀ x,HasDerivAt f 0 x) (v:ℝ): f v=f 0:= is_const_of_deriv_eq_zero (fun i=>(h i).differentiableAt) (fun i=>(h i).deriv) v 0
lemma Near.alone (h: Near b F) (r:ℤ) (H : ∀ w:List (Lane4 G), Course b w→ r<w.length → (F 0) w=0) : ∀ w:List (Lane4 G), Course b w→ r ≤ w.length→ ∀ i, F i w=F 0 w:= by
    obtain ⟨v, hv⟩:=h.limit; let m:=v.toNat+1
    have ht w (he:m≤ List.length w)(i:ℝ): F i w=0:= hv i w (by unfold m at he; omega)
    suffices he:∀ a:ℕ, a≤m → ∀ w,Course b w→a≤ List.length w→ r≤ List.length w→∀ i,F i w=F 0 w from fun w hu h' i=> he 0 (by omega) w hu (by omega) h' i
    intro a hq; induction hq using Nat.decreasingInduction with
    | self=> exact fun w h hx H i=> by rw [ht w hx,ht w hx]
    | of_succ n hm ih=>
        intro w hw hh he i; apply constancy (f:=fun t:ℝ=>F t w); intro x; rw [← show Wiref G F x w=0 from ?_]; exact h.pays x w hw;
        change orbit (Cpu G x) μzone (F x) w=0; rw [finite_cc μzone (period0 μzone cour0 (main_f _) h.touch)];
        unfold Ccy; have hz (p:QP):trc (Cpu G x) p (F x) w=0:= by
             rw [at_trc]; refine Finset.sum_eq_zero (fun z _=> Finset.sum_eq_zero (fun y _=>?_));
             have hQ : Course b ((z,p)::(y,-p)::w):=fun t=>by simp [hw t]
             rw [ih _ hQ (by simp; omega) (by simp; omega), H _ hQ (by simp; omega),mul_zero]
        -- K placeholder
        simp_rw [hz]; simp
lemma Near.gone (h: Near b F) (he:∀ w, Course b w→ (F 0) w=0) (w) (ht:Course b w): F t w=0:= (h.alone (-1) (fun w h _=> he w h) w ht (by omega) t).trans (he w ht)
lemma Touch_near {g:ℤ} (h:Bon b g F)(hh:Bon b g H)(hp:Sat A F P) (hx:Sat A' H P) (hv:Rank F u)(hr:Rank H v): Near false (F-H) where
   touch:= by rw [sub_eq_add_neg]; have he := TouchF.add h.joint (TouchF.scale (-1:ℂ) hh.joint); convert he using 1; ext; simp
   limit:= ⟨u ⊔ v, Rank.sub (hv.pay (le_sup_left)) (hr.pay le_sup_right)⟩
   pays t w _:= by convert! (hp.2 t w).sub (hx.2 t w) using 1; rw [map_sub]; simp only [Pi.sub_apply,Pi.add_apply]; abel
lemma Dprecise (h:Near false F) (he:Limit (F 0) r): Rank F r∧ (∀ w:List (Lane4 G), (w.length:ℤ)=r→∀ t:ℝ,F t w=F 0 w):= by
   have hT := h.alone r (fun w _=> he w); exact ⟨fun t w hw=> (hT _ (fun u=> Bool.noConfusion u) (by omega) t).trans (he w hw),fun w hw t=> hT w (fun u=> Bool.noConfusion u) hw.ge t⟩
lemma Dtotal (h:Near false F)(he:F 0=0): F=0:= by ext t w; exact h.gone (fun v _=>by rw [he]; rfl) w (fun u=>Bool.noConfusion u)
end YM.MS.Wind
