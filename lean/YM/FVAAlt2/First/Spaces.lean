import YM.FVAAlt2.First.Earn
import YM.Pert.Rig.Tested
/-! PP schedule geometry.kt frame. Reuse exact centering. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Subspace
open Function Finset Filter Topology Lattice
open Set Metric MeasureTheory
open MS MS.Koszul MS.Menus MS.Book MS.Theater MS.Tone MS.Vista MS.Fleet MS.High MS.Tide MS.Orbit MS.Rake MS.Dial MS.Land
open Extraction
open Pert Pert.Orb PertExtension PertExtension.LatticePT Profiles
open Pairing
open Real
open scoped Topology BigOperators ContDiff PowerSeries
variable {d:ℕ}{q:Side}{n j:ℕ}{K:Set (Points d)} (μ:ℝ)
local notation "ε"=>epsilon q n
local notation "Λ"=>Full.period q n
lemma center_code (i: Side)(h:4 ∣ i.val): (Lattice.lift (Full.center i))=fun _=>((i.val/4:ℕ):ℤ) := by
 apply Lattice.lift_eq_iff.mpr; refine ⟨?_,fun _=>?_⟩; · ext k; symm; change (((( (i.val/4:ℕ):ℤ )):ZMod i.val)) = _; simp only [Int.cast_natCast];rfl
 have hi:= i.property; change -(i.val:ℤ)<2*((i.val/4:ℕ):ℤ) ∧ 2*((i.val/4:ℕ):ℤ)≤ i.val; constructor; · apply lt_of_lt_of_le (b:=(0:ℤ)) (by exact neg_lt_zero.mpr (show 0<(i.val:ℤ) from by exact_mod_cast hi)); positivity
 exact_mod_cast ( show 2*(i.val/4)≤ i.val from Nat.le_trans (Nat.mul_le_mul_right (i.val/4) (by decide : 2≤4)) (Nat.mul_div_le i.val 4))
lemma center_budget (i:Side) (h:4∣i.val): pdist (Full.center i)=i.val/4:= by
 obtain ⟨j,hj⟩:= axis_max (Full.center i); rw [ hj ]; change (Lattice.lift (Full.center i) j ).natAbs=_; rw [center_code i h]; rfl
def hold (q:Side)(n:ℕ): Side:= ⟨2*q.val^(n^2+n+1),by positivity⟩
lemma launchSide (q:Side)(n:ℕ): periodN (hold q n)= Full.period q n:= by apply Subtype.ext; change 2*_ = _; unfold hold Full.period; norm_num; omega
lemma epsilon_here (q:Side)(n:ℕ): Full.topSpacing q n=epsilon q n:= by unfold Full.topSpacing epsilon; rw [zpow_neg,zpow_natCast]
lemma spending (h:1<q.val) (r:ℝ) : ∀ᶠ i:ℕ in atTop,r*Θ q i ≤ log ( (dimT (hold q) i).val:ℝ ) :=by
 filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop r)] with i hi; have hp(i:ℕ): (dimT (hold q) i).val = 4 * q.val^(i+1)*q.val^(i^2) := by rw [show dimT (hold q) i= _ from launchSide q i]; change 4* q.val ^ (i^2+i+1) = _; ring
 rw [hp]; push_cast; rw [log_mul (by positivity) (by positivity), log_pow ]; have H:= Real.log_nonneg (show (1:ℝ) ≤ 4*(q:ℝ)^(i+1) from (by
    have he: (1:ℝ) ≤ (q:ℝ)^(i+1) := one_le_pow₀ (by exact_mod_cast h.le); linarith)); apply le_add_of_nonneg_of_le H ?_; unfold Θ; push_cast; have he : 0< log (q:ℝ):= log_pos ( by exact_mod_cast h ); nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi (show 0≤(i:ℝ) from Nat.cast_nonneg _)) he.le]
structure StepP (q:Side)(K:Set (Points d)) where
 level:ℕ
 x: Full.Grid (Full.period q level) d
 inK: Full.embedding (Full.topSpacing q level) x∈K
local notation "u"=> StepP q K
def stopP (q:Side)(K:Set (Points d)):= Filter.comap (@StepP.level d q K) atTop
-- note Θ.w: full-
def poster (q:Side)(K:Set (Points d))(μ:ℝ) : Trial (StepP q K) (Fin d) where
 profile:={ θ i:= Θ q i.level, η i:=μ- Θ q i.level, room i:= theta_nonneg q i.level }
 side i:=hold q i.level
 head i:=Lattice.lift (Full.center ( Full.period q i.level ))
 off j i:= Lattice.lift ( i.x j - Full.center (Full.period q i.level) )
local notation "Φ"=> poster q K μ
set_option quotPrecheck false
local notation "γ"=> (Φ).profile
lemma visit_k (i:u): dimT ((Φ).side) i= Full.period q i.level:= launchSide q i.level
lemma enoughCash (i:u): Lobby.spacing Φ i= Full.topSpacing q i.level := by rw [epsilon_here]; exact theta_sc ..
lemma poster_width : Vista.width (Φ).side (Φ).head:= by apply centered_size; intro i; change (Φ).head i=Lattice.lift (wrap (dimT (Φ).side i) ((Φ).head i)); rw [visit_k, show (Φ).head i= Lattice.lift (Full.center (Full.period q i.level)) from rfl,wrap_lift]
lemma poster_clear : Clearance (Φ).side (Φ).head:= by
 intro i v; let n:= Full.period q i.level
 have hh:(dimT (Φ).side i).val=n.val:=by rw [visit_k]
 have ht : (dimT (Φ).side i).val ≤8*pdist (wrap (dimT (Φ).side i) ((Φ).head i)) ∧ 4*pdist (wrap (dimT (Φ).side i) ((Φ).head i))≤ (dimT (Φ).side i).val:= by
   rw [visit_k, show (Φ).head i= Lattice.lift (Full.center (Full.period q i.level)) from rfl,wrap_lift]
   have ht : 4∣(Full.period q i.level).val:=( show 4∣4*_ from dvd_mul_right 4 _ ); rw [ center_budget _ ht ]; omega
 exact remote _ ht.1 ht.2 v
lemma framesS (i:u): Dial.testP Φ i= realize (Full.embedding (Full.topSpacing q i.level) i.x):= by
 funext k; rw [Dial.testP,Tide.lifted,show exp _= _ from enoughCash μ i]; rfl
lemma profileW (hK:IsCompact K): Profile (Φ).profile (Φ).off:= by
 intro w
 let f(x:Points d):= realize x w
 have hf : Continuous f:= ( continuous_apply w ).comp ( realize_s ); obtain ⟨r,H⟩:= (hK.image hf.norm).bddAbove
 set a:=1+max 0 r
 have ha:0<a:=by unfold a; linarith [le_max_left 0 r]
 refine ⟨a,ha,fun i=>?_⟩
 have hp : ‖exp (-(γ).θ i) • embed ((Φ).off w i)‖≤ a:=by
    apply le_trans (b:=r) _ (by unfold a; linarith [le_max_right 0 r]); change ‖Dial.testP Φ i w‖≤_; rw [framesS]; apply H; exact ⟨ Full.embedding (Full.topSpacing q i.level) i.x,i.inK,rfl⟩
 rw [norm_smul_of_nonneg (exp_pos _|>.le),exp_neg,←div_eq_inv_mul] at hp; exact ( div_le_iff₀ (exp_pos ((Φ).profile.θ i)) ).mp hp

lemma poster_mesh (hK:IsCompact K)(h:K⊆conf d): Mesh (Φ).profile (info (Φ).off):= by
 apply Dial.unpose (v:=μ); intro i j he; let c(x:Points d):= ‖realize x i-realize x j‖
 have hc : Continuous c:= by unfold c; fun_prop
 obtain ⟨m,hm⟩:= (hK.image hc).bddAbove
 have hz:∃ a:ℝ,0<a∧∀ x∈K,a≤ c x:= by
   cases Set.eq_empty_or_nonempty K with
   | inl h=> exact ⟨1,zero_lt_one,fun x he=> (Set.notMem_empty x ( h ▸ he )).elim⟩
   | inr hx=> obtain ⟨x,hx,ht⟩:= hK.exists_isMinOn hx hc.continuousOn; exact ⟨ c x,norm_pos_iff.mpr (sub_ne_zero.mpr ((realize_one (h hx)).ne he)),ht⟩
 have hv(x:StepP q K): ‖(Tide.lifted (Φ).profile (Φ).off i-Tide.lifted (Φ).profile (Φ).off j) x‖= c (Full.embedding (Full.topSpacing q x.level) x.x):=by change ‖Dial.testP Φ _ _-Dial.testP Φ _ _‖=_; rw [framesS]
 obtain ⟨a,ha,h⟩:=hz; set b:=1+max 0 m; have hb:0<b:=by unfold b; linarith [le_max_left 0 m]
 refine ⟨⟨ b,hb,fun x=>?_⟩,⟨ a,ha,fun x=>?_⟩⟩ <;> rw [hv x] <;> simp only [Rake.Geo.roots,frameF, Pi.zero_apply,Real.exp_zero, mul_one]
 · exact le_trans (hm ( Set.mem_image_of_mem c x.inK )) (by unfold b; linarith [le_max_right 0 m])
 exact h _ x.inK
lemma books (hq:1<q.val)(hK:IsCompact K)(h:K⊆conf d): Dial.Uses Φ (stopP q K) μ:= ⟨profileW μ hK,poster_mesh μ hK h,rfl_t, Tendsto.comp (g:=Θ q) (grows hq) tendsto_comap, fun x=> Filter.Eventually.filter_mono (le_refl _) ((tendsto_comap (f:=StepP.level)).eventually (spending hq x)), poster_clear _,poster_width _ ⟩
 where rfl_t i:= rfl -- Lean infer?

end YM.FVAAlt2.Home.Subspace
