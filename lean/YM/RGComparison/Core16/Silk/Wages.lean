import YM.RGComparison.Core16.Silk.Sail
/-!
# Application: exponential clustering of the Fk word moments in finite periods
With Θ folklore HO calibration post-gate (B Lumen). NOT from a conditional uniqueness on equations
without constructing actual f_n price family. Momentum also paying over far tickets in Seal.Limit.
True formal prescription (via Sector Stencil Helm Vacuum T) not deriving IR independence from estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Push.Uniform Precision Finset Matrix
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side}{ι k T A D L I: Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype I]
variable {X:Shelf G A D} {P:Planet X S ι k T}

-- actual rooted covariance forecast. No large p.N assumption. Ball bill uses nearest separation.
def blank (X:Shelf G A D) (Y:Good X) (r d:ℕ):ℝ := (issued Y r d).choose
lemma blank_nn {Y:Good X} (r d:ℕ):0≤blank X Y r d:=(issued Y r d).choose_spec.1
lemma coupon (Y:Good X) (H:P.Steady) (r d j:ℕ)(hj:j≤r){w:Rail G ι}(g:w.length ≤ d):|nth j (price P w)| ≤ blank X Y r d:=(issued Y r d).choose_spec.2 _ _ _ _ _ _ S P H w g _ hj

lemma robot {g f:Roll}(i:ℕ){c t:ℝ}(hc:∀ j≤ i,|nth j f|≤c)(ht:∀ j≤ i,|nth j g|≤t): |nth i (f*g)| ≤ (antidiagonal i).card*(c*t) := by
    have h0:0≤c:=(abs_nonneg _).trans (hc _ le_rfl)
    unfold nth; rw [PowerSeries.coeff_mul]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>c*t) (fun a ha=>?_)).trans_eq (by rw [sum_const,nsmul_eq_mul])); rw [abs_mul]; have hh:= mem_antidiagonal.mp ha; apply mul_le_mul (hc _ (by omega)) (ht _ (by omega)) (abs_nonneg _) h0

def floorQ (Y:Good X)(d n k:ℕ):= blank X Y n (k+d)+(antidiagonal n).card*(blank X Y n k*blank X Y n d)
lemma floor_nn (Y:Good X)(n k d:ℕ):0≤floorQ Y d n k:=by unfold floorQ; exact add_nonneg (blank_nn ..) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (blank_nn ..) (blank_nn ..)))
lemma ice (Y:Good X)(H:P.Steady){w u:Rail G ι}{d l n:ℕ}(h:w.length ≤ d)(he:u.length ≤ l): |nth n (gap P w u)| ≤ floorQ Y d n l:= by
    unfold gap nth; rw [map_sub]; exact (abs_sub ..).trans (add_le_add (coupon Y H n _ _ le_rfl (by simp at *; omega : (u++w).length ≤ l+d)) (robot n (fun j hj=> coupon Y H n _ _ hj he) (fun j hj=> coupon Y H n _ _ hj h)))

def Distant (P: Planet X S ι k T)(w u: Rail G ι)(d:ℕ): Prop:= ∀ i∈w,∀ j∈u,d≤ separation (P.loc i.1) (P.loc j.1)

omit [Fintype ι] [Fintype k] [Fintype T] [Fintype D] [Fintype A] in
private lemma mirror (w:Rail G ι)(P : Planet X S ι k T) (d:ℕ): ∃ f:ι→ℕ, (∀ z∈w, f z.1=0) ∧ Lease P f ∧ ∀ i, (∀ j∈w,d≤ separation (P.loc j.1) (P.loc i)) → d ≤ f i:= by
    induction w with
    | nil=> exact ⟨fun _=>d, fun _ h=> by simp at h,⟨fun i j=>Nat.le_add_right d _⟩,fun i _=>le_rfl⟩
    | cons a u hp=>
       obtain ⟨f,hf,h,hk⟩:=hp; let F i:= separation (P.loc a.1) (P.loc i)
       refine ⟨fun i=> min (F i) (f i),fun i hi=>?_,⟨fun i j=>?_⟩,fun i he=> le_min (he a (List.mem_cons_self ..)) (hk i fun _ h=>he _ (List.mem_cons_of_mem _ h))⟩
       · dsimp only; rcases List.mem_cons.mp hi with hz|hz
         · subst i; rw [show F a.1 =0 from separation_self _]; exact min_eq_left (Nat.zero_le _)
         rw [hf i hz]; exact min_eq_right (Nat.zero_le _)
       have H:= h.lag i j; have h:F i≤ F j+separation (P.loc i) (P.loc j):= by rw [separation_comm (P.loc i)]; exact separation_triangle (P.loc a.1) (P.loc j) (P.loc i)
       omega

lemma braid {w:Rail G ι} {f:ι→ℕ}(H:P.Steady)(h: ∀ z∈w, f z.1=0)(hf:Lease P f)(e:ℕ)(hw:w.length≤e): Balance (floorQ (X:=X) H.prices e) P f (gap P w):= by
    refine ⟨hf,?_ ,fun r d u h=> ice H.prices H hw h,fun i w' hv=> absent_wick P H i w (fun j hj=>?_) w'⟩
    · rw [gap,List.nil_append,zero_part H, one_mul,sub_self] -- P implicit?
    intro he; have ht:= hv i (List.mem_cons_self ..); rw [he,h j hj] at ht; omega

-- α-inverse exp paid explicitly. Path f derived from pair displacement also if w empty
-- (then choose constant n). This Estimate includes full oriented Kit.H. Words budgets after all
-- charges, F coefficients connected (via 2-subtree product). Includes all periods not post-limits.
def Past (X:Shelf G A D)(C:ℝ)(r l d:ℕ): Prop:= ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(S:Side)(P:Planet X S ι k T), P.Steady → ∀ j≤r, ∀ w:Rail G ι,List.length w ≤ l→∀ u:Rail G ι,u.length ≤ d → ∀ e,Distant P w u e→|nth j (gap P w u)|≤C / costLamp X e
lemma silence (Y:Good X) (r l d:ℕ):∃ C:ℝ,0≤C ∧ Past X C r l d:=by
    choose f hf h using fun i:Fin (r+1)=> treatment X (floorQ Y l) (i:ℕ) d
    let T:=∑ i,f i; refine ⟨T,sum_nonneg (fun i _=>hf i),fun _ _ _ _ _ _ S P H i hi w hw u hu e he=>?_⟩
    obtain ⟨v,h0,hv,hp⟩:= mirror w P e; refine (h ⟨i,by omega⟩ _ _ _ _ _ _ S P H v _ (braid H h0 hv l hw) u hu e (fun k hk=>hp _ fun j hj=>he j hj k hk)).trans (div_le_div_of_nonneg_right ?_ coin_pos.le)
    exact single_le_sum (fun i _=>hf i) (mem_univ _)
end YM.RGComparison.Core16.Silk
