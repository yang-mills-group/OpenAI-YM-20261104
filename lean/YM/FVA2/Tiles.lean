import YM.FVA2.Matched

/-!
# Power ladders on the separated inversion-even physical geometry.

`static frames` spacing `q^-n`, top full side `8*q^(n+n*n)`. Terminal
side 8 (may extend), measurement length 1. Particular comparison family
 meeting log P ~ n^2 and integer division needs (also when q a power of 3).
Flex center box agrees with usual center average, works pointwise. In files importing this one aim also
a compact-neighborhood uniform scalar error whose constant is NOT chosen after each
volume/point. Need also scale prices for center and marked offsets with explicit inequalities.
No smoothing of positions in this file.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Tiles
open Function Filter Topology Metric MeasureTheory
open MS MS.Local.Physical MS.Plane MS.Landau MS.Book MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom MS.Puff.SplitP MS.Native.Wilsonian MS.Menus MS.Fleet MS.Swirl MS.Swirl.Near
open MS.Rake MS.Land MS.Tide MS.Orbit MS.Tone MS.Vista MS.Tide.PeakT MS.Dial
open Source Channel Score Matched Lattice
open scoped Topology Classical ContDiff
variable {G: Gauge} {B: Deck G} {O: Booked B} (b: MS_Data G O) (φ:NativeDictionary B)
variable {I W:Type}[LinearOrder W](q: Side) (hL: q.val>1)
variable (μ:ℝ) (w: W→ Label B)

-- terminal ratio choices.Joint reset lengths.
def cells (i:ℕ): ℕ:= q.val^(i+i*i)
lemma cells_one (i:ℕ): 0<cells q i:= pow_pos q.property _
def roof (i:ℕ): Side:=⟨4*cells q i, mul_pos (by norm_num) (cells_one ..)⟩
theorem fullSide (i:ℕ): (dimT (roof q) i).val=8*q.val^(i+i*i):= by rw [dimT,cap_val]; change 2*(4* _) = _; unfold cells; ring
lemma level_multiple (i j:ℕ)(h:j≤ i+i*i): ∃ v:ℕ, v>0 ∧ (dimT (roof q) i).val= 8*v*q.val^j:= by
    let e:= i+i*i-j; refine ⟨ q.val^e, pow_pos q.property e,?_⟩; rw [ fullSide, mul_assoc 8, ← pow_add, show e+j = i+i*i from (by omega)] -- omega unfold e may not.
def clock (q:Side)(i:ℕ):ℝ:= (i:ℝ)* Real.log q.val
lemma clock_scale (i:ℕ) : Real.exp (clock q i) = (q.val:ℝ)^i:= by rw [clock,Real.exp_nat_mul, Real.exp_log (show 0<(q.val:ℝ) from Nat.cast_pos.mpr q.property)]
lemma lights (i:ℕ) : 0 ≤ clock q i:= mul_nonneg (by positivity) (Real.log_nonneg (show 1≤(q.val:ℝ) from (Nat.one_le_cast.mpr q.property)))
def physical (q:Side) (i:ℕ) := Real.exp (-clock q i) * ( (dimT (roof q) i).val:ℝ)
theorem logPeriod (i:ℕ) : Real.log ( physical q i )=Real.log 8+ (i:ℝ)^2 * Real.log q.val := by
    have hv : 0<(q.val:ℝ):= Nat.cast_pos.mpr q.property; rw [physical,Real.log_mul (by positivity) (by positivity),Real.log_exp,fullSide]; push_cast; rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]; push_cast; unfold clock; ring
include hL
lemma forward : Tendsto (clock q) atTop atTop:= by
    apply Tendsto.atTop_mul_const (Real.log_pos (by exact_mod_cast hL : 1 < (q.val:ℝ))) tendsto_natCast_atTop_atTop -- signature
lemma wax : Super atTop (roof q) (clock q):= by
    have hv:= (show 0<(q.val:ℝ) from Nat.cast_pos.mpr q.property); have L:= Real.log_pos (by exact_mod_cast hL : 1<(q.val:ℝ))
    intro c; filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop c)] with i hi
    apply le_of_le_of_eq _ ( (show Real.log (tickA (roof q) i) = clock q i + Real.log (physical q i) from ?_).symm ); swap
    · rw [physical, Real.log_mul (by positivity) (by positivity), Real.log_exp ]; unfold tickA; ring
    rw [ logPeriod ]; unfold clock; exact le_trans (b:= (i:ℝ)*( (i:ℝ) * Real.log (q.val:ℝ))) (mul_le_mul_of_nonneg_right hi (mul_nonneg (by positivity) L.le)) (by nlinarith only [ mul_nonneg (show 0≤(i:ℝ) by positivity) L.le, Real.log_pos (show 1<(8:ℝ) by norm_num)])
omit hL

-- geometry.Canopy for offsets.Integer center margin. no user group/smoothing needed.
def Daily (q:Side)(i:ℕ)(x:Lattice.Cover): Prop:=∀ j: Axis, ↑(cells q i)≤ x j ∧ x j≤↑(2*cells q i)
variable (i:ℕ)
lemma someDay : Daily q i (fun _=>(cells q i:ℤ)):= by intro _; exact ⟨le_refl _, by dsimp only; omega⟩
lemma ownDay {x:Lattice.Cover} (h:Daily q i x): Lattice.lift (Lattice.wrap (dimT (roof q) i) x)=x:= by
    apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro j; rw [fullSide]; obtain hh:=h j; have hp:= cells_one q i; 
    have hv : ↑(8 * ↑q ^ (i+i*i):ℕ) = (8:ℤ) * (cells q i) := by rw [ Int.natCast_mul ]; rfl
    omega -- coercion of Nat pow?
lemma clearance {x:Lattice.Cover} (h:Daily q i x) (y:Half): mine (dimT (roof q) i) (wrap (dimT (roof q) i) x-thin (roof q i) y):= by
    let n:=dimT (roof q) i; let w:=wrap n x; have hp(y:Half)(h:y ≠ 0): pdist (thin (roof q i) y)=4*cells q i:= Eq.trans ( caress .. ) (by rw [bornlf y h,Nat.mul_one]; rfl)
    have hw:LE.le (pdist w) (2*cells q i):= by
        unfold pdist w; rw [ ownDay q i h ]; apply Finset.sup_le; intro j _; obtain hh:= h j; omega
    have ht:=component_le w 0; unfold w at ht; unfold n at ht; rw [ ownDay q i h ] at ht; have ht': cells q i≤pdist w:= by obtain hx:= h 0; dsimp [w,n]; omega
    unfold mine; nth_rw 1 [show (dimT (roof q) i).val= 8*cells q i from fullSide ..]; change 8*cells q i≤16*pdist (w-thin (roof q i) y)
    by_cases hz:y=0; rw [hz,map_zero,sub_zero]; omega
    have hP:pdist (thin (roof q i) y) ≤ pdist w + pdist ( w-thin (roof q i) y ):= by nth_rw 1 [ show thin (roof q i) y=w+(-(w-thin (roof q i) y)) from (by abel) ]; exact (pdist_triangle ..).trans_eq (by rw [ pdist_neg ])
    specialize hp y hz; omega

section shape
-- round.Down common mesh


def mesh (w:ℝ)(x:QP): Lattice.Cover:= fun i=>⌊Real.exp w*x i⌋
-- fractional center later.V
lemma mesh_size (w:ℝ)(x:QP): ‖Tone.embed (mesh w x) - Real.exp w • x‖≤1:= by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; apply abs_le.mpr; have he:= Int.floor_le (Real.exp w * x j); have hv:= Int.lt_floor_add_one (Real.exp w * x j); change -(1:ℝ)≤ ((⌊Real.exp w * x j⌋:ℤ):ℝ) - Real.exp w * x j ∧ ((⌊Real.exp w * x j⌋:ℤ):ℝ) - Real.exp w * x j ≤ 1; constructor <;> linarith
lemma unmesh (w:ℝ)(x:QP): ‖Real.exp (-w) • Tone.embed (mesh w x) - x‖ ≤ Real.exp (-w):= by
    let V:=Tone.embed (mesh w x); rw [Real.exp_neg, show (Real.exp w)⁻¹ • V-x=(Real.exp w)⁻¹ • (V-Real.exp w • x) from (by rw [smul_sub,inv_smul_smul₀ (Real.exp_ne_zero _)]), norm_smul_of_nonneg (by positivity) ]; exact mul_le_of_le_one_right (by positivity) (mesh_size w x)
-- Allows centers varying; cut initial finite lengths off by monotone ι.I sets.Trial all sequences.M

def film (W I:Type)(p:I→ℕ)(q:Side)(μ:ℝ)(z:I→ Lattice.Cover)(c: W→ I→ Lattice.Cover): Trial I W:= ⟨ ⟨ fun i=> clock q ( p i ),fun i=> μ-clock q (p i),fun i=> lights q (p i)⟩,roof q ∘ p,c,z ⟩

variable (p:I→ℕ)(l: Filter I)(z:I→ Lattice.Cover)(Z:∀ i,Daily q (p i) (z i))
local notation "P"=>fun c=>film W I p q μ z c
include hL Z
omit [LinearOrder W] in
lemma warm {c}(hz:Tendsto p l atTop)(he:Tide.Profile (P c|>.profile) ( W:=W ) c)(hx: Mesh (P c|>.profile) ( W:= W ) ( Fleet.info c )): Uses (P c) l μ:= ⟨ he,hx,fun _=>rfl,(forward q hL).comp hz,fun x=> hz.eventually (wax q hL x),fun i x=>clearance q (p i) (Z i) x, centered_size _ _ fun i=>(ownDay q _ (Z i)).symm⟩
omit Z
-- version normal frames at literal support X separated approximate.Measurements.
variable (u:W→QP) (h:Injective u)
local notation "V"=>P (fun w i=>mesh (clock q (p i)) (u w))

omit [LinearOrder W] in
lemma marches (hz:Tendsto p l atTop) : Tendsto ( testP V ) l (𝓝 u):= by
    apply tendsto_pi_nhds.mpr; intro w; apply tendsto_iff_dist_tendsto_zero.mpr; simp_rw [dist_eq_norm]; exact squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) (Eventually.of_forall fun i=> unmesh _ (u w)) (Real.tendsto_exp_atBot.comp ( tendsto_neg_atTop_atBot.comp ( (forward q hL).comp hz ) )) -- instance Pi Fint? not.
include h Z
lemma high_clamp (hz:Tendsto p l atTop)(hh:∀ i, Clamp u ( testP V i )) : Uses V l μ:= by
    unfold film; apply warm q hL μ p l z Z hz ?_ ?_ -- check order
    · intro w; refine ⟨ 1+‖u w‖,by positivity,fun i=>?_⟩; let s:=clock q (p i); let x:=u w; let f:=Tone.embed (mesh s x)
      change ‖f‖ ≤ _; apply le_trans (b:=1+Real.exp s*‖x‖) ?_ ?_
      · calc
           _ = ‖( f- Real.exp s • x )+ Real.exp s • x‖ := by rw [sub_add_cancel]
           _ ≤ _:= by apply le_trans (norm_add_le ..); rw [norm_smul_of_nonneg (Real.exp_pos _).le]; gcongr; exact mesh_size ..
      change _ ≤ ( 1+‖x‖)* Real.exp s; have hh:= Real.one_le_exp (lights q (p i)); unfold s; linarith
    apply Dial.unpose (v:=μ); intro i j H; have hp :0<‖u i-u j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr ( h.ne H )); refine ⟨ ⟨ 2*‖u i-u j‖,by positivity, fun k=>?_⟩,⟨ ‖u i-u j‖/2,half_pos hp,fun k=>?_⟩⟩ <;> simp only [Geo.roots,Pi.zero_apply, Real.exp_zero,mul_one]; exact (hh _ i j H |>.2 ).le; exact (hh _ i j H |>.1).le -- k placeholder
end shape
-- construct with shifted startup, any daily centers throughout. beyond startup offset.Tech.
section data
variable (x:W→QP)[Fintype W]
abbrev ladder (x:W→QP)(q:Side)(μ:ℝ)(z:ℕ→Lattice.Cover)(m:ℕ):= film W ℕ (fun i=>i+m) q μ (fun i=> z (i+m) ) (fun w i=> mesh (clock q (i+m)) (x w) )
include hL
lemma ranges (hx:Injective x): ∃ m:ℕ,∀ z:ℕ→Lattice.Cover,(∀ i,Daily q i (z i))→ Uses ( ladder x q μ z m ) atTop μ ∧ Tendsto ( testP ( ladder x q μ z m )) atTop (𝓝 x):= by
   let z:ℕ→Lattice.Cover:=fun _=>0
   let F:Trial ℕ W:= film W ℕ id q μ z (fun w i=>mesh (clock q i) (x w))
   have he:Tendsto ( testP F ) atTop (𝓝 x):= marches q hL μ id atTop z x tendsto_id
   obtain ⟨i,hi⟩:= eventually_atTop.mp ( he.eventually ( earlyW hx ) ); refine ⟨ i,fun K hK=>?_⟩; let g:ℕ→ℕ:= (·+i); have hp : Tendsto g atTop atTop:= (show StrictMono g from fun _ _ h=>Nat.add_lt_add_right h i).tendsto_atTop; have hh j: Clamp x ( testP ( ladder x q μ K i ) j ) := hi (j+i) (by omega); exact ⟨ high_clamp q hL μ g atTop _ (fun _=> hK _) x hx hp hh, marches q hL μ g atTop _ x hp⟩
lemma reaches (T:Land.Prescription B)(h:Matched.AllProfiles b φ T)(hx:Injective x):
    ∃ m:ℕ,∀ z:ℕ→Lattice.Cover,(∀ i,Daily q i (z i))→ let p:= ladder x q μ z m; Uses p atTop μ ∧
            ∀ (s:Finset W)(n:ℕ),
      Tendsto ( fare ( Label.h ∘ w ) p.profile (Matched.ordinary φ p T μ w ) s n ) atTop (𝓝 ( Dial.tour b w μ x s n )) ∧
      PeakT.twin atTop p.profile mildG ( fare ( Label.h ∘ w ) p.profile ( Matched.ordinary φ p T μ w ) s n ) (fun i=>Dial.tour b w μ ( testP p i ) s n) := by
    obtain ⟨m,hm⟩:=ranges q hL μ x hx; exact ⟨ m,fun z hZ=> ⟨ (hm z hZ).1,fun s n=> ⟨ (Matched.on_positions b φ _ T μ w atTop h (hm z hZ).1 hx (hm z hZ).2 s n).2, (Matched.accuracy b φ _ T μ w atTop h (hm z hZ).1 s n).2⟩ ⟩ ⟩
end data
end YM.FVA2.Tiles
