import YM.FormalBulk08.Roof.Amount

/-! Convolution solve in well-order; be used for numerical product costing. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Roof
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I : Type*} [Fintype I][DecidableEq I]
variable {s w:I→ℕ}{T W : Pennants I}{b : I → ℝ}
variable (h:Colfax s w T b)(ht:W*T=1)

omit ht h [DecidableEq I] in
lemma subpays (W T:Pennants I)(l i j): coeff l ((W*T) i j)=∑ k, ∑ t∈Finset.antidiagonal l,coeff t.1 (W i k)*coeff t.2 (T k j):= by
    rw [Matrix.mul_apply,map_sum]; exact Finset.sum_congr rfl fun i _=> coeff_mul ..
omit ht h [DecidableEq I] in
lemma slope_sum (W T:Pennants I)(i j) : coeff 0 ((W*T) i j)=∑ k,coeff 0 (W i k)*coeff 0 (T k j) := by rw [subpays]; simp
include h ht
lemma climb_inverse (i j:I)(e:ℕ)(hx:s j+e<s i) : coeff e (W i j)=0:= by
    induction e using Nat.strong_induction_on generalizing j with
    | _ e ih =>
      generalize hp : priority s w j=k
      induction k using Nat.strong_induction_on generalizing j with
      | _ k hk=>
        have hh : coeff e (W i j)*b j=0:= by
           symm; rw [show (0:ℝ)=coeff e ((W*T) i j) by rw [ht,Matrix.one_apply_ne (show i ≠ j from fun z=>by subst i;omega),map_zero], subpays, Finset.sum_eq_single j]; swap
           · intro x _ hb; apply Finset.sum_eq_zero; rintro ⟨p,q⟩ hv; rw [Finset.mem_antidiagonal] at hv
             by_cases h': coeff q (T x j)=0
             · rw [show coeff (p,q).2 (T x j)=0 from h', mul_zero]
             have hp' : s x≤ s j+q:= le_of_not_gt fun hP=>h' (h.bound x j q hP)
             have hz : coeff p (W i x)=0:= by
                rcases q with _ | q
                · apply hk (priority s w x) (by rw [←hp]; exact promotes (h.peers _ _ h' hb)) x (by omega) rfl |> ((show p=e from by omega).symm ▸ ·) -- bad
                exact ih p (by omega) x (by omega)
             exact mul_eq_zero.mpr (Or.inl hz)
           swap; · simp
           rw [Finset.sum_eq_single (e,0)]; swap
           · rintro ⟨p,q⟩ hv hu; rw [Finset.mem_antidiagonal] at hv; have hx':p<e:=by
                by_contra hr
                have hh : p=e:=by omega
                have hq:q=0:= by omega
                exact hu (Prod.ext hh hq)
             exact mul_eq_zero.mpr (Or.inl (ih p hx' j (by omega)))
           swap; · simp
           rw [show coeff (e,(0:ℕ)).2 (T j j)= b j from h.due j]
        exact (mul_eq_zero.mp hh).resolve_right (h.paid j).ne'
lemma stop_inverse (i j:I)(hs:s i=s j)(hw:w i≤w j) : coeff 0 (W i j)=if i=j then (b j)⁻¹ else 0:= by
    generalize hp: priority s w j=k
    induction k using Nat.strong_induction_on generalizing j with
    | _ k hk=>
      have he : coeff 0 ((1:Matrix I I Pence) i j)=coeff 0 (W i j)* b j:= by
         rw [←ht,slope_sum,Finset.sum_eq_single j,h.due];swap
         · simp
         intro x _ hx; by_cases he:coeff 0 (T x j)=0
         · rw [he,mul_zero]
         obtain hl | hh:= h.peers x j he hx
         · rw [climb_inverse h ht i x 0 (by omega),zero_mul]
         rw [hk (priority s w x) (hp ▸ promotes (Or.inr hh)) x (hs.trans hh.1.symm) (hw.trans hh.2.le) rfl,if_neg (show i≠x from fun z=> by rw [z] at hw;exact hh.2.not_ge hw),zero_mul]
      by_cases hx:i=j
      · subst i; rw [Matrix.one_apply_eq,coeff_one,if_pos rfl] at he; rw [if_pos rfl]; exact mul_right_cancel₀ (h.paid j).ne' (he.symm.trans (inv_mul_cancel₀ (h.paid j).ne').symm)
      rw [Matrix.one_apply_ne hx,map_zero] at he; rw [if_neg hx]; exact (mul_eq_zero.mp he.symm).resolve_right (h.paid j).ne'
lemma Colfax.reclaims : Colfax s w W (fun i=> (b i)⁻¹):= ⟨climb_inverse h ht,fun i=>inv_pos.mpr (h.paid i),stop_inverse h ht⟩
omit ht
lemma Colfax.back : Colfax s w (show Matrix I I Pence from T⁻¹) (fun i=> (b i)⁻¹):= h.reclaims (Matrix.nonsing_inv_mul T h.det)
end YM.FormalBulk08.Roof
