import YM.Contacts.Model.Access
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
namespace Province
open Slope Arbor Lintel.Plata ConnectedActivityE6 Next.Fluctuations Blaze Sienna
open Boulevard (actual throng stillA sunny)
variable {A H Z t C Λ I μ:ℝ}{S:ℝ≥0}{d v:ℕ}{B:BudgetPoint}{X:G.ColorIndex}{P:Bed}{L:Side}
def foot (z:ℕ):=max 1 (z-7)
def tiles (z:ℕ)(i:Stars):Side:= ⟨2*(foot z+i.val), Nat.mul_pos zero_lt_two <| Nat.le_add_right _ _|>.trans' (le_max_left ..)⟩
lemma wings (z:ℕ):∀ i:Stars,(tiles z i).val=2*(foot z+i.val):= fun _=>rfl
def witness (z:ℕ):Side:= ⟨2*(10*z+1),by omega⟩
variable (z k) (T:PathData G)(F:bore G)(p:Clip)
local notation "Y" => tiles z
def bough (i:ℕ) : Story G:= energy p T F (wings z) (k+3) i
local notation "Zz" => bough k z T F p
local notation "S₀" => witness z
def proceeds (i:ℕ): ℝ:= deposit (pass (Zz i) (S₀))
def slice (i:ℕ): Story G:= Zz i-flange G (proceeds k z T F p i)
lemma adapted_piece (i:ℕ):Adapted (slice k z T F p i):= fun s U=>congr_arg₂ (·-·) (paints _ s U) (flange_spin _ s U)
variable {k z}
lemma foot_v (hz:20≤z): foot z+5≤z:=by unfold foot; omega
lemma holds_local (hz:20≤z) : LocalOn (Lattice.box z) (Zz i):= by exact hue_loc _ (local_clock (wings z) _ (by have hx:=foot_v hz; omega))
lemma slice_local (hz:20≤z) (i:ℕ): LocalOn (Lattice.box z) (slice k z T F p i) := fun U V h=> congr_arg₂ (·-·) (holds_local T F p hz U V h) (flange_local _ (by omega) U V h)
section body
variable (h:Aegis X F P)(hT:T.Bounds p μ I Λ)(hG:G.Simple)
variable (hx:∀ m,Dial P p T m)(ha:∀ m,Orbit T (hair F m) p)
variable (hk:2≤k) (hz:20≤z) (hi:i≤k)
include h hT hz hi
lemma arb_bill (B:BudgetPoint)(u:Site m): B.Regular (neighbors z u) (pass (Zz i) m u):= oak B F p T hT h (by omega) (wings z) (by have ht:=foot_v hz; omega) u -- order
lemma atlas (B:BudgetPoint)(u:Site m): B.Regular (neighbors z u) (pass (slice k z T F p i) m u):= reg_sub (arb_bill T F p h hT hz hi _ _) (face_bill _ _ (by omega))
include hG
lemma identities (B:BudgetPoint)(m:Side)(hu:2*z < m.val): proceeds k z T F p i= deposit (pass (Zz i) m) := includes hG (holds_local T F p hz) (arb_bill T F p h hT hz hi B 0) (arb_bill T F p h hT hz hi B 0) (by change 2*z< 2*(10*z+1); omega) hu -- hG include
include hk hx ha hG
omit hz in
private lemma undimmed (u:Site m)(x:Link G m)(hj:j<hero i): jet (pass (Zz i) m u ∘ input G m) j x=0:= by
   apply eroded F hG h p T hT (wings z) (fun i=> hx _) (fun i=> ha _) x _ _ u <;> unfold hero at * <;> omega -- order
omit hk in
lemma decline (B:BudgetPoint)(hx':i<3): proceeds k z T F p i=0:= concession (H:=arb_bill T F p h hT hz hi B) (m:=witness z) (r:=10*z+1) (by rfl) (by omega) (by change 10*z< 2*(10*z+1); omega) hG F h p T hT (wings z) hx' hi (fun i=>hx _) (fun i=>ha _)
omit hG hx ha hk hz in
lemma germSlice (u:Site m): altitude (pass (slice k z T F p i) m u):= by obtain ⟨s,hs⟩:= paint_supply G 0; exact (energy_apt F h p T hT _ (by omega) _).sub (show AnalyticAt ℝ (pass (flange G (proceeds k z T F p i)) m u ∘ input G m) 0 from (cloverly _ (fun i=> imprints hs (show ‖(0:Link G m)‖≤1 by simp) i) u).analytic.analyticAt)
omit hz in
lemma slice_unit (u:Site m): pass (slice k z T F p i) m u 1=0:= by
   have he:= undimmed (z:=z) T F p h hT hG hx ha hk hi u 0 (j:=0) (lt_of_lt_of_le zero_lt_two (owned i))
   simp only [jet_zero,input_zero,comp_apply] at he; change pass (Zz i) m u 1- pass (flange G (proceeds k z T F p i)) m u 1=_; rw [he,forms]; simp [VerifiedReset.counter, VerifiedReset.quad]
lemma lease_vanish (B:BudgetPoint)(m:Side)(u:Site m)(x:Link G m)(hj:j<hero i) : jet (pass (slice k z T F p i) m u ∘ input G m) j x=0:= by
    have hf : jet (pass (Zz i) m u ∘ input G m) j x=0:= undimmed T F p h hT hG hx ha hk hi u x hj
    by_cases hl:j<2; swap; · have ht:proceeds k z T F p i=0:= decline _ _ _ h hT hG hx ha hz hi B (by unfold hero at *; omega); unfold slice; rw [ht,show flange G 0=0 from (by ext; simp [flange]),sub_zero]; exact hf
    have hv:= slice_unit (z:=z) T F p h hT hG hx ha hk hi u
    -- use palm.Point affine gradient for F gauge to vanish rank1; use clover analytic dip?
    interval_cases j; · simp only [jet_zero,comp_apply,input_zero]; exact hv
    let a:= pass (slice k z T F p i) m u; let U:= a ∘ increment 1; let L: Link G m →L[ℝ] Directions G m:= ContinuousLinearMap.pi fun v: Bond m=> (ContinuousLinearMap.proj (v.1, Exterior.coord v.2)).comp (arm G m 1).toContinuousLinearMap; have he: a ∘ input G m= U ∘ L:= by funext v; apply congr_arg a; funext ⟨x,y⟩; erw [encode_link,increment,mul_one]; rfl --
    have h:= atlas T F p h hT hz hi B u; have hh:=flat_critical hG h; change fderiv ℝ U 0=0 at hh; change jet (a∘input G m) 1 x=0; rw [he,jet,iteratedFDeriv_one_apply,fderiv_comp, L.map_zero, hh]; simp; exact (show L 0=0 from L.map_zero).symm ▸ (germ_diff h).differentiableAt (by norm_num); exact L.differentiableAt
omit hx ha hk in
lemma wreck (B:BudgetPoint)(u:Site m) (ht:10*z< m.val): let f:=pass (slice k z T F p i) m u; ∀ x y, IsAffineDirection u x → IsAffineDirection u y → logHessian f x y=0:= rescinded B hG (identities T F p h hT hG hz hi B m (by omega)) (arb_bill T F p h hT hz hi B) (paints _) (by omega) ht
end body
end Province
end YM.Contacts.Model
