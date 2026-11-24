import YM.FormalBulk08.Spigot.Niv
-- D spectral inversions use only Wilson linear algebra from this supplementary
-- *accepted* library, not MS conversion/prescription; same gauge uncolored.
import YM.MSbar.Tree.Resolvent
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
Riemann sums including the full potential frequency cut (horizontal
representative via symbol D, mode zero omitted, evaluate only gauge jets).
Simple functions in a rectangular radian chart. Use *all* true periods
for the definition; don't differentiate a coupling cutoff limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
abbrev Pitch := Axis→ℝ
def hop (n:Side):ℝ:=2*Real.pi/n.val
def tone (n:Side)(y:Cover):Pitch:=fun i=>hop n*(y i:ℤ)
lemma pitch_high (n:Side):0<hop n:= by unfold hop; positivity
lemma tone_maps (p:Site n) : axes (tone n (Lattice.lift p))=mon p:= by ext i; simp [axes,tone,hop,mon,reciprocal]; ring

def block (n:Side)(p:Cover):Set Pitch:= Set.univ.pi fun i:Axis=> Ico (tone n p i) (tone n p i+hop n)
lemma in_block (x:Pitch)(p:Cover):x∈block n p ↔∀ i,tone n p i≤x i ∧ x i<tone n p i+hop n := mem_univ_pi
lemma square_price (n:Side)(p:Cover):volume.real (block n p)=hop n^4 := by
    unfold block; rw [measureReal_def, Real.volume_pi_Ico_toReal (a:=tone n p) (b:=fun i=>tone n p i+hop n) (fun _=>by linarith [pitch_high n])]; simp
lemma square_finite (n:Side)(p:Cover):volume (block n p) ≠ ⊤:=fun h=> by have he:=square_price n p; rw [measureReal_def,h,ENNReal.toReal_top] at he; exact pow_ne_zero _ (pitch_high n).ne' he.symm
lemma block_meas (n:Side)(p:Cover):MeasurableSet (block n p):= MeasurableSet.univ_pi (fun _=> measurableSet_Ico)

def meterTile (x:Pitch)(n:Side) : Cover := fun a=> ⌊x a/hop n⌋
lemma slot_map (x:Pitch)(n:Side)(p:Cover): x∈block n p ↔ meterTile x n=p:= by
    have h (i:Axis): tone n p i ≤ x i ∧ x i< tone n p i+hop n ↔ meterTile x n i=p i := by
        have he:=pitch_high n; unfold meterTile;rw [Int.floor_eq_iff,le_div_iff₀ he,div_lt_iff₀ he]; simp [tone,mul_comm,add_mul]
    rw [in_block]; simp_rw [h]; exact ⟨funext,fun h=>congr_fun h⟩
lemma enjoys (x:Pitch)(n:Side)(p:Cover)(h:x∈ block n p): dist x (tone n p)≤hop n:= by
   rw [dist_eq_norm]; refine (pi_norm_le_iff_of_nonneg (pitch_high n).le).mpr (fun i=>?_); obtain ⟨ha,hb⟩:= (in_block _ _).mp h i; rw [Real.norm_eq_abs,Pi.sub_apply,abs_of_nonneg (sub_nonneg.mpr ha)]; linarith

lemma inside (x:Pitch)(n:Side):x∈block n (meterTile x n):= (slot_map ..).2 rfl
lemma inner_reflected (p:Site n): ‖tone n (Lattice.lift p)‖≤ Real.pi:= by
    apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr; intro i; exact Further.FreeCovariance.KP.local_price p i
lemma just_over (p:Cover)(h:‖tone n p‖<Real.pi): Lattice.lift (wrap n p)=p:= by
   refine Lattice.lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩; have ha: ‖tone n p i‖ < Real.pi:=lt_of_le_of_lt (norm_le_pi_norm ..) h; rw [Real.norm_eq_abs,abs_lt] at ha; unfold tone hop at ha; have hv:0<(n.val:ℝ):=by positivity
   obtain ⟨hh,hp⟩:=ha; field_simp at hh hp
   have he : - (n.val:ℝ)<2*(p i):= by nlinarith [Real.pi_pos]
   have hk : 2*(p i:ℝ) < n.val:= by nlinarith [Real.pi_pos]
   exact_mod_cast And.intro he hk.le
lemma hefty (p:Site n)(hp:p≠0): hop n ≤ ‖tone n (Lattice.lift p)‖:= by
   obtain ⟨i,hi⟩:=Function.ne_iff.mp (show Lattice.lift p≠0 from fun h=> hp ((Lattice.wrap_lift ..).symm.trans ((congr_arg (wrap n) h).trans (map_zero (wrap n)))))
   refine le_trans ?_ (norm_le_pi_norm _ i); simp only [tone,norm_mul,Real.norm_of_nonneg (pitch_high n).le];apply le_mul_of_one_le_right (pitch_high n).le; rw [Real.norm_eq_abs,← Int.cast_abs]; exact_mod_cast (show (1:ℤ)≤|Lattice.lift p i| from Int.add_one_le_of_lt (abs_pos.mpr hi))
lemma ebb:Tendsto hop atTop (𝓝 0):= by
    have he:Tendsto (fun i:Side=>(i.val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp North.highlim; unfold hop; simpa only [div_eq_mul_inv, mul_zero] using (show Tendsto (fun n:Side=>2*Real.pi*((n.val:ℝ))⁻¹) atTop (𝓝 (2*Real.pi*0)) from (tendsto_inv_atTop_zero.comp he).const_mul _)
lemma guided (x:Pitch): Tendsto (fun n:Side=>tone n (meterTile x n)) atTop (𝓝 x):= by rw [tendsto_iff_dist_tendsto_zero]; exact squeeze_zero (fun _=>dist_nonneg) (fun n=>by rw [dist_comm]; exact enjoys _ _ _ (inside x n)) ebb
lemma veil (p:Pitch)(h:‖p‖< Real.pi): ∀ᶠ n:Side in atTop, Lattice.lift (wrap n (meterTile p n))=meterTile p n:= ((guided p).norm.eventually (gt_mem_nhds h)).mono fun _ q=> just_over _ q
lemma bleak (x:Pitch)(h:Real.pi<‖x‖):∀ᶠ n:Side in atTop,∀ v:Site n,x∉block n (Lattice.lift v):= by
   filter_upwards [ebb.eventually (gt_mem_nhds (sub_pos.mpr h))] with n hn p hp; have hz:= enjoys x _ _ hp; linarith only [hn,(norm_sub_norm_le x (tone n (Lattice.lift p))),dist_eq_norm x (tone n (Lattice.lift p)),hz,inner_reflected p]
end YM.FormalBulk08.Avenue
