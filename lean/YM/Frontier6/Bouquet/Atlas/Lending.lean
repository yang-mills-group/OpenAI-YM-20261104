import YM.Frontier6.Bouquet.Atlas.Prices

/-! Slicing and anisotropic charge coincidence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Audit Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q:Ensemble }(i:P) (a:P→ℝ)
def outdoors : Set Room:= {x:Room|∃ j:P,j≠i∧ x∈ Accounts (normal j.val) (a j)}
lemma pathways : Accounts (normal i.val) (a i)∪ outdoors i a= paths P a:=by
    ext1 x; constructor
    · rintro (hx|⟨j,h,hx⟩); exacts [⟨i,hx⟩,⟨j,hx⟩]
    rintro ⟨j,hx⟩; by_cases he:j=i; exacts [Or.inl (he ▸ hx),Or.inr ⟨j,he,hx⟩]
lemma outside : outdoors i a ⊆ (Loft (fiber P) (normal i.val) : Set Room):= by
    rintro x ⟨j,he,hj⟩; exact ⟨normal_orth (P.pairwise j.property i.property (fun hh=> he (Subtype.ext hh))) hj.1,home_sub j.property hj.1⟩
lemma paths_lesser (h:P≤Q)(g:Q→ℝ): paths P (g ∘ assign h) ⊆ paths Q g:=fun x ⟨i,hi⟩=>⟨_, normal_sub (inside h i) hi.1,(show ‖x‖≤g (assign h i) from hi.2)⟩
lemma estimate_multiply (X:Place)[FiniteDimensional ℝ X]{n:ℕ}{u C C':ℝ}{f:X→ℂ}{g:Full X}(hf:Smooth f)(hu:0≤u)(h: Charge n u f C)(ht:Charge n u g C'):Charge n u (screen f hf g) ( (2:ℝ)^n*C*C'):= Estimate.mul h ht h.nonneg ht.nonneg hu hf g.contDiff
lemma Checks.pane_global {C C' r:ℝ}{g:normal i.val→ℂ} (hg: Smooth g){f:Full (fiber P)} {n:ℕ}(hp:Charge n (a i) g C)(he:tsupport f⊆ cylindrical _ _ (closedBall (0:normal i.val) r))(ht:0<a i)(h:Checks (fiber P) (paths P a) f (n+n) C'): Checks (fiber P) (paths P a) (paneM g hg f) n ((2:ℝ)^n*C*C'):=by
    rw [← pathways i a] at *; exact Elevator.exports _ (Elevator.panes (home_sub (P:=P) i.property) g hg) ht ht.le he h (outside i a) (fun i _ h=> estimate_multiply _ _ ht.le hp h)

variable {n:ℕ}{a B:ℝ}
namespace Court
variable {i} (Z:Court i)
lemma global_cost (n:ℕ) : ∃ C:ℝ,0 ≤ C ∧∀ x:P→ℝ,0<x i→∀ b r A:ℝ,0<b→ ∀ f:Full (fiber P),Z.Contains (x i) f → tsupport f⊆ cylindrical _ _ (closedBall (0:normal i.val) r) → Checks (fiber P) (paths P x) f (n+n) A → Checks (fiber P) (paths P x) ((common b).film P Z.split f) n (C*A):=by
    obtain ⟨C,hC,H⟩:= cures (X:=normal i.val) n (scars P Z.split); let R:=max 1 (4/Z.clearance); have hr:1 ≤ R:= le_max_left ..
    let D:=(2:ℝ)^n*(R^n*C); have hz:0 ≤ D:=by unfold D; have hh:0<R:=zero_lt_one.trans_le hr; positivity
    refine ⟨max D 1,hz.trans (le_max_left ..),fun x hx b r A hb f h hv hX=>?_⟩
    by_cases hp : 4*b<Z.clearance*x i
    · rw [Z.film_delayed hx hb h hp]; exact (Checks.low hX (by omega)).cost_mono (le_mul_of_one_le_left hX.nonneg (le_max_right ..))
    let F': normal i.val→ℂ:= fun v : normal i.val=> (common b).cutter (scars P Z.split) v.val; have ht:x i ≤ R*b:=by
       apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) hb.le); rw [div_mul_eq_mul_div]; apply (le_div_iff₀ Z.pos).mpr; linarith
    have hB: Charge n (x i) F' (R^n*C):= Estimate.scale_up (H b hb) hb.le hx.le hC hr ht
    rw [Z.film_alone]; exact (Checks.pane_global i x _ hB hv hx hX).cost_mono (mul_le_mul_of_nonneg_right (le_max_left ..) hX.nonneg)
end Court
end YM.Frontier6.Bouquet.Atelier
