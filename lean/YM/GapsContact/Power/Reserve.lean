import YM.GapsContact.Power.Water

/-!
# Inter-scale substitution

Portions of SharpGram.Balance, here for true lower fields real money, valid also
complex operations. Use at every scale past a threshold (later discharge at small lengths).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Analysis Table Extraction Spec OS
open Push.FiniteDetection.Free OPE.Levy Ascent
open scoped Topology BigOperators Classical NNReal InnerProductSpace
variable {G:Gauge}{L:Register G}{T:Table L} (H:T.Hierarchy) (P:DiffPlan T) {d e n:ℕ}{r s:ℝ}

local instance (d : ℕ) : FiniteDimensional ℝ (T.Field d) := Module.Finite.trans ℂ _

abbrev Good (d:ℕ)(r:ℝ):Prop:=∀ x:T.Field d, x≠0 → 0<chip H d r x
lemma bankable (hr:0<r)(h: Good H d r) : Bijective (bond H d r):=by
   have he : Injective (bond H d r):= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x hx=>by
      by_contra hh; have ht:bond H d r x x=0:=LinearMap.congr_fun hx x
      rw [← bond_root H hr] at ht; exact absurd ht (pow_pos (h x hh) 2).ne')
   exact ⟨he,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by change _=Module.finrank ℝ (Module.Dual ℝ _); rw [Subspace.dual_finrank_eq])).1 he⟩

abbrev Up (P:DiffPlan T)(d:ℕ) := P.rise (Nat.le_succ d)
private abbrev Rise (d:ℕ) := (Up P d).restrictScalars ℝ

def edge (d:ℕ) (r:ℝ) : T.Field (d+1) →ₗ[ℝ] T.Field d:=
   if h: Bijective (bond H d r) then ((LinearEquiv.ofBijective (bond H d r) h).symm.toLinearMap ∘ₗ (LinearMap.dualMap (Rise P d))) ∘ₗ (bond H (d+1) r : T.Field (d+1) →ₗ[ℝ] Module.Dual ℝ (T.Field (d+1))) else 0

def ridge (d:ℕ) (r:ℝ) : T.Field (d+1) →ₗ[ℝ] T.Field (d+1) := LinearMap.id - (Rise P d).comp (edge H P d r)
lemma ridged (r:ℝ) (x:T.Field (d+1)): ridge H P d r x=x-Up P d (edge H P d r x):=rfl

def sip (d:ℕ) (r:ℝ)(x:T.Field (d+1)):ℝ:= chip H (d+1) r (ridge H P d r x)
lemma sip_nn (d:ℕ)(r:ℝ)(x:T.Field (d+1)):0 ≤ sip H P d r x:= chip_nn ..
lemma sip_cont (d:ℕ)(hr:0<r):Continuous (sip H P d r):=(chip_cont H _ r hr).comp (LinearMap.continuous_of_finiteDimensional _)

variable (h:P.Inclusions T)(hP:P.Orientation H.spin)(hr:0<r)(hg:Good H d r)
include hr hg
lemma edger (x:T.Field (d+1)): bond H d r (edge H P d r x)=(bond H (d+1) r x).comp (Rise P d):= by
   unfold edge; rw [dif_pos (bankable H hr hg)]; exact (LinearEquiv.ofBijective _ (bankable H hr hg)).apply_symm_apply _
include h hP
lemma edged (x:T.Field d): edge H P d r (Up P d x)=x:= (bankable H hr hg).1 (by
   rw [edger H P hr hg]; exact LinearMap.ext (fun y=> Eq.symm (bond_inherit H P h hP _ hr x y)))
lemma ridge_low (x:T.Field d):ridge H P d r (Up P d x)=0:=by rw[ridged,edged H P h hP hr hg,sub_self]
lemma edge_high (x:T.Field (d+1)):edge H P d r (ridge H P d r x)=0:=by rw[ridged,map_sub, edged H P h hP hr hg,sub_self]
lemma ridge_alt (x:T.Field (d+1)) (s:ℝ):ridge H P d r (ridge H P d s x)=ridge H P d r x:=by rw[ridged (r:=s),map_sub,ridge_low H P h hP hr hg,sub_zero]
lemma siphon (x:T.Field (d+1)): chip H (d+1) r x ^ 2= (chip H d r (edge H P d r x))^2 + sip H P d r x ^ 2 := by
   let y:=edge H P d r x; let z:=ridge H P d r x; let U:= Up P d; let M:=bond H (d+1) r
   have hu:x=U y+z:=by unfold U y z; rw [ridged]; abel
   have hx : M z (U y)=0:=by have he:= edger H P hr hg z; rw [show edge H P d r z=0 from edge_high H P h hP hr hg _,map_zero] at he; exact LinearMap.congr_fun he.symm y
   change _ = (chip H d r y)^2 + (chip H (d+1) r z)^2; rw [chip_inherit H P h hP (Nat.le_succ d) hr y]; nth_rw 1 [hu]; rw [bond_root H hr,bond_root H hr,bond_root H hr];
   change (M (U y+z)) (U y+z)=_; change _=M (U y) (U y)+M z z; have he: M (U y) z=M z (U y):= bond_symm H hr (U y) z; simp [he,hx]
lemma edge_le (x:T.Field (d+1)): chip H d r (edge H P d r x) ≤ chip H (d+1) r x:= by
    apply (sq_le_sq₀ (chip_nn ..) (chip_nn ..)).mp; rw [siphon H P h hP hr hg]; exact le_add_of_nonneg_right (sq_nonneg _)
lemma sip_le (x:T.Field (d+1)): sip H P d r x ≤ chip H (d+1) r x:= by
    apply (sq_le_sq₀ (sip_nn ..) (chip_nn ..)).mp; rw [siphon H P h hP hr hg]; exact le_add_of_nonneg_left (sq_nonneg _)
lemma sip_leaves {x y:T.Field (d+1)}(hh:x-y∈LinearMap.range (Up P d)):sip H P d r x=sip H P d r y:=by
   rcases hh with ⟨b,hb⟩; rw [← sub_add_cancel x y,hb.symm]; unfold sip; rw [map_add,ridge_low H P h hP hr hg,zero_add]
omit h hP hr hg in
lemma sip_lt (h₀:Good H (d+1) r) (x:T.Field (d+1)): x∉LinearMap.range (Up P d) → 0<sip H P d r x:=by
   intro hh; apply h₀; intro he; rw [ridged] at he; exact hh ⟨_,(sub_eq_zero.mp he).symm⟩
lemma siphoned (x:T.Field (d+1))(s:ℝ):sip H P d r (ridge H P d s x)=sip H P d r x:=by unfold sip; rw[ridge_alt H P h hP hr hg]
lemma sip_go (hs:0<s)(hs':s≤ r)(x:T.Field (d+1)) : sip H P d r x≤ sip H P d s x:= by
    refine le_trans ((siphoned H P h hP hr hg x s).symm.trans_le (sip_le H P h hP hr hg _)) ?_
    exact power_signal H _ hs hs'
omit h hP hr hg in
lemma sip_smul (c:ℝ)(x:T.Field (d+1)): sip H P d r (c • x)= ‖c‖*sip H P d r x:=by unfold sip; rw [map_smul, ← Complex.coe_smul, chip_smul, Complex.norm_real]

end YM.GapsContact.Power
