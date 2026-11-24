import YM.FVA2.CompactRate
import YM.FVA2.Changed
/-!
# Regulator convention for literal PriceB vs Dial, side=8*q^(m+1+m*m)
 Proofs adapted Tiles/CompactRate. n-length.Press non-homogeneous allowed.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
namespace YM.FVA2.Pond
open Function Filter Topology Metric MeasureTheory
open MS MS.Local.Physical MS.Plane MS.Landau MS.Book MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom MS.Puff.SplitP MS.Native.Wilsonian MS.Menus MS.Fleet MS.Swirl MS.Swirl.Near
open MS.Rake MS.Land MS.Tide MS.Orbit MS.Tone MS.Vista MS.Tide.PeakT MS.Dial
open Source Channel Score Matched Lattice
open scoped Topology Classical ContDiff
variable {G: Gauge} {B: Deck G} {O: Booked B} (b: MS_Data G O) (φ:NativeDictionary B)
variable {I W:Type}[LinearOrder W](q: Side) (hL: q.val>1)
variable (μ:ℝ) (w: W→ Label B)

-- terminal ratio choices.Joint reset lengths.
def cells (i:ℕ): ℕ:= q.val^(i+i*i+1)
lemma cells_one (i:ℕ): 0<cells q i:= pow_pos q.property _
def roof (i:ℕ): Side:=⟨4*cells q i, mul_pos (by norm_num) (cells_one ..)⟩
theorem fullSide (i:ℕ): (dimT (roof q) i).val=8*q.val^(i+i*i+1):= by rw [dimT,cap_val]; change 2*(4* _) = _; unfold cells; ring
lemma times (i:ℕ) : dimT (roof q) i= PertExtension.LatticePT.side q i:= by
   apply Subtype.ext; change (dimT (roof q) i).val= (PertExtension.LatticePT.side q i).val; rw [ fullSide ]; change _= 8*(q.val)^(i+1)*q.val^(i^2); rw [ show i+i*i+1=i+1+i^2 from (by rw [pow_two]; omega), pow_add,mul_assoc]
lemma level_multiple (i j:ℕ)(h:j≤ i+i*i+1): ∃ v:ℕ, v>0 ∧ (dimT (roof q) i).val= 8*v*q.val^j:= by
    let e:= i+i*i+1-j; refine ⟨ q.val^e, pow_pos q.property e,?_⟩; rw [ fullSide, mul_assoc 8, ← pow_add, show e+j = i+i*i+1 from (by omega)] -- omega unfold e may not.
def clock (q:Side)(i:ℕ):ℝ:= (i:ℝ)* Real.log q.val
lemma clock_scale (i:ℕ) : Real.exp (clock q i) = (q.val:ℝ)^i:= by rw [clock,Real.exp_nat_mul, Real.exp_log (show 0<(q.val:ℝ) from Nat.cast_pos.mpr q.property)]
lemma lights (i:ℕ) : 0 ≤ clock q i:= mul_nonneg (by positivity) (Real.log_nonneg (show 1≤(q.val:ℝ) from (Nat.one_le_cast.mpr q.property)))
lemma ticket (i:ℕ) : PertExtension.LatticePT.epsilon q i=Real.exp (-clock q i):= by rw [ Real.exp_neg,clock_scale ]; rfl
def physical (q:Side) (i:ℕ) := Real.exp (-clock q i) * ( (dimT (roof q) i).val:ℝ)
theorem logPeriod (i:ℕ) : Real.log ( physical q i )=Real.log 8+ (i:ℝ)^2 * Real.log q.val+Real.log q.val := by
    have hv : 0<(q.val:ℝ):= Nat.cast_pos.mpr q.property; rw [physical,Real.log_mul (by positivity) (by positivity),Real.log_exp,fullSide]; push_cast; rw [Real.log_mul (by positivity) (by positivity),Real.log_pow]; push_cast; unfold clock; ring
include hL
lemma forward : Tendsto (clock q) atTop atTop:= by
    apply Tendsto.atTop_mul_const (Real.log_pos (by exact_mod_cast hL : 1 < (q.val:ℝ))) tendsto_natCast_atTop_atTop -- signature
lemma wax : Super atTop (roof q) (clock q):= by
    have hv:= (show 0<(q.val:ℝ) from Nat.cast_pos.mpr q.property); have L:= Real.log_pos (by exact_mod_cast hL : 1<(q.val:ℝ))
    intro c; filter_upwards [(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually (eventually_ge_atTop c)] with i hi
    apply le_of_le_of_eq _ ( (show Real.log (tickA (roof q) i) = clock q i + Real.log (physical q i) from ?_).symm ); swap
    · rw [physical, Real.log_mul (by positivity) (by positivity), Real.log_exp ]; unfold tickA; ring
    rw [ logPeriod ]; unfold clock; exact le_trans (b:= (i:ℝ)*( (i:ℝ) * Real.log (q.val:ℝ))) (mul_le_mul_of_nonneg_right hi (mul_nonneg (by positivity) L.le)) (by nlinarith only [L,mul_nonneg (show 0≤(i:ℝ) by positivity) L.le, Real.log_pos (show 1<(8:ℝ) by norm_num)])
omit hL

-- geometry.Canopy for offsets.Integer center margin. no user group/smoothing needed.
def Daily (q:Side)(i:ℕ)(x:Lattice.Cover): Prop:=∀ j: Axis, ↑(cells q i)≤ x j ∧ x j≤↑(2*cells q i)
variable (i:ℕ)
lemma someDay : Daily q i (fun _=>(cells q i:ℤ)):= by intro _; exact ⟨le_refl _, by dsimp only; omega⟩
lemma ownDay {x:Lattice.Cover} (h:Daily q i x): Lattice.lift (Lattice.wrap (dimT (roof q) i) x)=x:= by
    apply lift_eq_iff.mpr ⟨rfl,?_⟩; intro j; rw [fullSide]; obtain hh:=h j; have hp:= cells_one q i; 
    have hv : ↑(8 * ↑q ^ (i+i*i+1):ℕ) = (8:ℤ) * (cells q i) := by rw [ Int.natCast_mul ]; rfl
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

def film (W I:Type)(p:I→ℕ)(q:Side)(μ:ℝ)(z:I→ Lattice.Cover)(c: W→ I→ Lattice.Cover): Trial I W:= ⟨ ⟨ fun i=> clock q ( p i ),fun i=> μ-clock q (p i),fun i=> lights q (p i)⟩,roof q ∘ p,c,z ⟩

variable (p:I→ℕ)(l: Filter I)(z:I→ Lattice.Cover)(Z:∀ i,Daily q (p i) (z i))
local notation "P"=>fun c=>film W I p q μ z c
include hL Z
omit [LinearOrder W] in
lemma warm {c}(hz:Tendsto p l atTop)(he:Tide.Profile (P c|>.profile) ( W:=W ) c)(hx: Mesh (P c|>.profile) ( W:= W ) ( Fleet.info c )): Uses (P c) l μ:= ⟨ he,hx,fun _=>rfl,(forward q hL).comp hz,fun x=> hz.eventually (wax q hL x),fun i x=>clearance q (p i) (Z i) x, centered_size _ _ fun i=>(ownDay q _ (Z i)).symm⟩
omit Z hL

-- Index supplies Uniformity. Existing Material from CompactRate. Same proof with profile size adjusted for side_f.
open CompactRate (disjoint under upper open_disjoint)
variable {U: Set ( W→ Tone.QP )} (hp: U⊆ disjoint W)(hC:IsCompact U) (ψ: Warehouse G)(A:Land.Prescription B)(B0: MixedStory.AllProfiles b ψ A)
include hp hC
local notation "σ"=> A.team
local notation "dκ"=> Label.h ∘ w
local notation "Φ"=> tFees A w
local notation "ℶ"=> fun i:ℕ=> dimT (Pond.roof q) i
def markedPrice (n:Side)(θ:ℝ)(u:Lattice.Cover)(d: W→Lattice.Cover)(s:Finset W) : T ℂ:= Port.τ (Vane.charge dκ s) θ • netE (Track.ticketRead ψ n dκ σ (μ-θ) Φ u d s)
def site (q:Side)(i:ℕ)(d:W→Lattice.Cover) : W→ Tone.QP:= fun w=> Real.exp (-clock q i) • Tone.embed (d w)
variable [Fintype W]

-- large index encodes uniformity. If no points at a scale no assertion.E.t eventually.
structure Index (W:Type)(U:Set ( W→ Tone.QP )) (q:Side) where
    i : ℕ
    c : Lattice.Cover
    d : W→Lattice.Cover
    daily : Daily q i c
    alive : site q i d∈U
local notation "ι"=> Index W U q
local notation "l"=> Filter.comap Index.i (atTop) -- type implicit.
local notation "ρ"=> film W ι Index.i q μ Index.c (fun w (i:ι)=>i.d w)
include hL
lemma admission : Dial.Uses ρ l μ:= by
    apply warm _ hL μ Index.i (l) Index.c Index.daily tendsto_comap
    · intro w; obtain ⟨R,hR,hK⟩:= upper hC; refine ⟨ R,hR,fun i=>?_⟩; let s:=clock q i.i; let p:=site q i.i i.d; change ‖Tone.embed ( i.d w )‖≤ R*Real.exp s; rw [ ← div_le_iff₀ (Real.exp_pos s) ]; let q':= Tone.embed (i.d w); have hx : ‖( p w )‖≤ R:= le_trans (norm_le_pi_norm ..) (hK _ i.alive); change ‖Real.exp (-s) • q'‖≤_ at hx; rw [ norm_smul_of_nonneg (Real.exp_pos _).le, Real.exp_neg ] at hx; rw [div_eq_mul_inv, mul_comm]; exact hx
    obtain ⟨R,hR,hK⟩:=upper hC; apply Dial.unpose (v:=μ); intro i j H
    obtain ⟨ r,hr,ht⟩:= under hp hC i j H; refine ⟨ ⟨ 2*R,by positivity,fun k=>?_⟩,⟨ r,hr,fun k=>?_⟩ ⟩ <;> simp only [ Geo.roots, Real.exp_zero, Pi.zero_apply, Pi.sub_apply,mul_one ]; · change ‖site _ k.i k.d i-site _ k.i k.d j‖ ≤ _; rw [two_mul]; exact ((norm_sub_le ..)|>.trans (add_le_add ((norm_le_pi_norm ..)|>.trans (hK _ k.alive)) ((norm_le_pi_norm ..)|>.trans ( hK _ k.alive))))
    exact ht (site q _ k.d) k.alive
include B0
-- comparison rate for ordinary (and can use cumulant equivalent from Matched.accuracy)
theorem power (s:Finset W)(n:ℕ) : ∃ C:ℝ,0<C∧∃ m:ℕ,∀ j≥m,∀ a:Lattice.Cover,Daily q j a→∀ d:W→Lattice.Cover,site q j d∈U→
    dist (markedPrice μ w ψ A ((ℶ) j) (clock q j) a d s n) (Dial.tour b w μ (site q j d) s n ) ≤ C*Real.exp (-mildG*(clock q j)):= by
    obtain ⟨C,h,H⟩:= (MixedStory.accuracy b ψ ρ A μ w l B0 (admission q hL μ hp hC) s n |>.2).2; obtain ⟨m,hm⟩:= eventually_atTop.mp ( eventually_comap.mp H ); refine ⟨ C,h,m,fun j hj a hA d hd=>?_⟩; rw [ dist_eq_norm ]; exact hm j hj ⟨ j,a,d,hA,hd⟩ rfl -- ramp rfl


omit B0 hp hC hL
open PertExtension.LatticePT Real in
lemma fromToday (x: PertExtension.LatticePT.Native q i)(hf:x∈ origins q i): Daily q i (Lattice.lift x):= by
    let s:Lattice.Cover:=fun j=> ( (x j).val:ℤ ); let R₀:= PertExtension.LatticePT.side q i; have he: wrap R₀ s=x:= by ext j; change (↑((x j).val:ℤ):ZMod R₀.val)=x j; simp;
    let r:= PertExtension.LatticePT.buffer q i; have ht: r=cells q i := by unfold r PertExtension.LatticePT.buffer; rw [ ← times, fullSide ]; unfold cells; omega
    have hv: Daily q i s:= by intro j; obtain hp: ( buffer q i≤ (x j).val ∧ _ ):= ( Finset.mem_filter.mp hf ).2 j; change r≤ (x j).val∧ (x j).val≤2*r at hp; change _ ≤ ( ↑((x j).val):ℤ ) ∧ ( ↑((x j).val):ℤ ) ≤ _; omega
    obtain hw:= ownDay q i hv; rw [times] at hw; rw [show ( Lattice.lift x)=s from (he ▸ hw)]; exact hv
end YM.FVA2.Pond
