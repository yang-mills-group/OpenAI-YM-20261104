import YM.Contacts.Junction.Buyer
/-! # TurnBook in all-stage shots. Work at x=t-coarse and Θ step. Different period arbitrary.
 Keep prices over main budgets (`ε` not assumed concretely, use absorption by limits).
 -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge}{c f:Side}{S:StepData c f} (P : ChartRatio G) {Λ σ C e a v b d t K:ℝ}{n k j r:ℕ}
namespace Current
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer
-- local curry charts
section pull
variable {A E V : ℕ→ Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (A i)][∀ i,NormedSpace ℝ (A i)] [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]
variable {x:Meter}{W:∀ i,E i → A i}{z:∀ i,E i→V i}{f H:ℕ→ℝ}
attribute [local instance] Classical.propDecidable
lemma Rush.zeroN (k:ℕ) (h:x.Rush 0 f): x.Rush 0 (fun i=> f i^k):= by simpa only [zero_mul] using! h.powers k
lemma Rush.bb (h:x.Rush a f)(he:∀ᶠ i in atTop,0≤H i∧ H i≤ f i): x.Rush a H:= by apply h.view; exact he.mono fun i hi=> (Real.norm_of_nonneg hi.1).trans_le ((hi.2).trans (le_abs_self (f i)))
lemma polar (hx: Direct x k a f W)(hz: Direct x k a f z): Direct x k a f (fun i w=>(W i w,z i w)):= Budget.stack hx hz
lemma meetP (h:x.Rush d H)(hb:d≤0): Direct (E:=E) x k 0 H (fun _=>id):= Budget.id (Frame.head (h.mono hb))
variable {β:ℕ→Type}{u:Shelf E β A}{Y:Frame β E} {L:∀ i,A i→ V i}
lemma rUse (h:Direct x k a f L)(hv:∀ᶠ i in atTop,∀ z,u i z (Y i z)∈ Frame.Bank A f i)(he:Budget x Y k d u)(ht:d≤0) : Budget x Y k a fun i z=> L i ∘ u i z := Budget.graft (g:=fun i _ => L i) (Arms.port h hv) he ht
-- canonical use `Φ: E primary* st`: both projections
variable {Q : Shelf E β fun i=>(A i×V i)}
lemma fstD (h: Budget x Y k a Q): Budget x Y k a (fun i j v=> (Q i j v).1):= Budget.natural (fun i=>ContinuousLinearMap.fst ℝ (A i) (V i)) h fun _ _=> norm_fst_le _
lemma sndD (h: Budget x Y k a Q): Budget x Y k a (fun i j v=> (Q i j v).2):= Budget.natural (fun i=>ContinuousLinearMap.snd ℝ (A i) (V i)) h fun _ _=> norm_snd_le _
variable [∀ i,FiniteDimensional ℝ (V i)] {σ:ℕ→ℝ}{O:Lamp V}
lemma jetBudget (h: ∀ᶠ i in atTop, AnalyticAt ℝ (O i) 0∧ ∀ x:V i, ‖jet (O i) j x‖ ≤ H i* ‖x‖^j)(ht:x.Rush a H) : x.Rush a (fun i=> normJ j (O i) 0):= by
   let U i:= iteratedFDeriv ℝ j (O i) 0; let K :ℝ:= j.factorial; have hk:0< K:= by unfold K; positivity
   obtain ⟨R,hR,h'⟩:= Loom.poly_rent j; have hz: x.Rush a (fun i=>R*(K* |H i|)):= ((absolute ht).multiplier _).multiplier _; refine hz.view ?_; filter_upwards [h] with i hi; change ‖‖U i‖‖ ≤ _; rw [norm_norm]; apply le_trans _ (le_abs_self _); apply h' _ _ hi.1.contDiffAt.iteratedFDeriv_comp_perm _ (by positivity); intro y; have ht:‖K⁻¹ * Tensor.diagonal (U i) y‖ ≤ _:=hi.2 y; rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hk.le),inv_mul_le_iff₀ hk] at ht; apply ht.trans; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) hk.le
end pull
section wallet
variable {p:ℕ→Clip}{T:ℕ→PathData G}{F:ℕ→bore G}{A:ℕ→Bed}{N:Meter}
variable {B:ℕ→BudgetPoint}{X:ℕ→Side}{Λ v a d:ℕ→ℝ} {X₀: G.ColorIndex}{n:ℕ}{j:ℕ→ℕ} -- j shadow caution
local notation "M" => (fun i=> Milling.cap G (X i))
local notation "Y" => (fun i=> Link G (X i))
variable (hp: ∀ᶠ i in atTop,(T i).Bounds (p i) σ C (Λ i)) (hx:∀ᶠ i in atTop,∀ x≤k,Charted G k (N.β i) (B i) (T i) (F i) (p i) (d i) (ripe (N.β i)) (a i) x (j i))
    (he:∀ᶠ i in atTop,Aegis X₀ (F i) (A i))
variable (hG:G.Simple)(hh : ∀ᶠ i in atTop,10*(B i).B< (X i).val)(hV:N.Rush 0 fun i=> (Fintype.card (Site (X i)):ℝ))(ha:N.Rush 0 (fun i=>N.pow (a i) i)) (hd:∀ e,N.Rush e (fun i=> N.pow (-(d i)) i)) (hk:2≤ k)
local notation "W" => (fun i=>biomass k (B i) (F i) (p i) (T i) (f:=X i))
local notation "R" => (fun i=>boom k (B i) (F i) (p i) (T i) (f:=X i))
variable {E γ:ℕ→ Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
-- u uses actual nozzle or pole of cubic.Root
variable {Zr:Frame γ E}
lemma forStake {V:ℕ→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)]{Z: Shelf E γ (fun i=>ℝ×V i)} (h: Budget N Zr n 0 Z){P:ℕ→Lamp V}{b:ℝ}(hp:∀ i≤k, Budget N Zr n b (fun j x y=> P i j (Z j x y).2)): Budget N Zr n b (fun j x y=> stake (fun v z=>P v j z) (k+1) (Z j x y)) := by
   let Q : Mint E γ:= fun i x y=> (Z i x y).1; unfold stake; exact Loom.Budget.spike (a:=fun v i x z=> (Z i x z).1^v * P v i (Z i x z).2) (fun i (hi:i∈Finset.range (k+1))=> Budget.mul (Q^i) _ (Budget.power (fstD h) i) (hp i (Nat.le_of_lt_succ (mem_range.mp hi))) (by ring)) -- Fleet
include hp hx he hh hG hV hk hd
variable {Z : Shelf E γ (fun i=>Milling.cap G (X i))} (hZ: Budget N Zr n 0 Z)
include hZ
local notation "ζ" => (fun i j x=> Prod.snd (Z i j x))
lemma highP (u:ℕ)(h:u≤k)(r:ℝ): Budget N Zr n r (fun i j x=>Buyer.debt k (B i) (F i) (p i) (T i) u (f:=X i) (ζ i j x)):= by
    let t i:= deficit k (B i) (F i) (p i) (T i) u (f:=X i); let J i:= (Fintype.card (Site (X i)):ℝ)*N.pow (-d i) i; refine Budget.skew (w:=t) (j:=k+3-u) (sndD hZ) le_rfl (fun i hi=>?_); refine jetBudget (H:=J) ?_ (hV.times (hd r) (zero_add _)); filter_upwards [hp,hx,he,hh] with i hp hx hy hh;  
    exact ⟨(wind_ana ..).sub (highT hp hx h), fun x=> Buyer.bounty hp hx hk hG hy hh h (by omega) x ⟩
lemma gleaming (v:ℝ): Budget N Zr n v (fun i j=> R i∘ Z i j):= forStake hZ (P:=fun u i=> Buyer.debt k (B i) (F i) (p i) (T i) u (f:=X i)) (fun i hi=> highP hp hx he hG hh hV hd hk hZ i hi v) -- args order
omit hp he hk hG hh hd
include ha
lemma whirs (ht:∀ᶠ i in atTop,n≤j i)(hu:∀ᶠ i in atTop,∀ j,‖ζ i j (Zr i j)‖< ripe (N.β i)): Budget N Zr n 0 (fun i j=> W i∘ Z i j) := by
   let t k':Lamp Y:= fun i=> plays (Buyer.book k (B i) (F i) (p i) (T i) k' (f:=X i))
   let J i:= (Fintype.card (Site (X i)):ℝ)* N.pow (a i) i
   refine forStake hZ (P:=t) (fun i' hi=>?_);  apply rUse (L:=t i') (u:=ζ) ?_ (f:=fun i=> ripe (N.β i)) (hu.mono fun a h i=> mem_ball_zero_iff.mpr (h i)) (sndD hZ) le_rfl; apply Meter.Funds.mk; have hv : N.Rush 0 J:= hV.times ha (by norm_num); refine ⟨J,hv,?_⟩
   filter_upwards [hx,ht,N.eventual] with i h ht hx; let c:= X i; have hb (v: Frame.Bank Y (fun i=>ripe (N.β i)) i): Allows n (t i' i) (v.val) (J i):= Model.train (k:=n) _ (fun j=> ((h i' hi).shine _ j _ (mem_ball_zero_iff.mp v.property).le).order ht)
   exact ⟨show 0≤J i from mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx.le _),fun z=> Brush.offer.2 ⟨(hb z).analytic.of_le le_top,(hb z).norm_le⟩⟩
end wallet
end Current
end YM.Contacts.Junction
