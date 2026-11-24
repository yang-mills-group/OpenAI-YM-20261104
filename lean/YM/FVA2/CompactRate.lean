import YM.FVA2.Tiles
/-!
# Uniform power-rate on lattice pins in compact separated sets

Compare to the continuum functions at those *same* relative positions. Use whole
spacing aᵢ and side of power-compatible primer. May later average physical anchors
or relative offsets or integrate against a continuous compactly supported measure
payment. Also supply uniform convergence (no rate stipulated here) for data sampled
instead using `mesh` and targeting unrounded positions. Key independence of center A
with rates constant uniform including change of torus phase origin.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.CompactRate
open Function Filter Topology Metric MeasureTheory
open MS MS.Local.Physical MS.Plane MS.Landau MS.Book MS.Book.Convolve MS.Puff MS.Puff.Actors MS.Puff.Engine MS.Puff.Mom MS.Puff.SplitP MS.Native.Wilsonian MS.Menus MS.Fleet MS.Swirl MS.Swirl.Near
open MS.Rake MS.Land MS.Tide MS.Orbit MS.Tone MS.Vista MS.Tide.PeakT MS.Dial
open Source Channel Score Matched Tiles Lattice
open scoped Topology Classical ContDiff
variable {G: Gauge} {B: Deck G} {O: Booked B} (b: MS_Data G O) (φ:NativeDictionary B)
variable (q:Side)(hq:q.val>1)(A:Land.Prescription B)(μ:ℝ)(B0: AllProfiles b φ A)
variable {W:Type}[LinearOrder W](w: W→ Label B)
-- also let expose at general size ℓ.S is physical units (native stone). N inversion=8*
local notation "σ"=> A.team
local notation "dκ"=> Label.h ∘ w
local notation "Φ"=> tFees A w
local notation "ℶ"=> fun i:ℕ=> dimT (Tiles.roof q) i

abbrev Place (W: Type):= W→ Tone.QP
def markedPrice (n:Side)(θ:ℝ)(u:Lattice.Cover)(d: W→Lattice.Cover)(s:Finset W) : T ℂ:= Port.τ (Vane.charge dκ s) θ • netE (ticketRead φ n dκ σ (μ-θ) Φ u d s)
def site (q:Side)(i:ℕ)(d:W→Lattice.Cover) : W→ Tone.QP:= fun w=> Real.exp (-clock q i) • Tone.embed (d w)
variable [Fintype W]
def disjoint (W:Type) := {x: Place W| Injective x}
local notation "P"=>Place W
variable {U: Set (W→ Tone.QP)} -- no P pitfall
variable (hp: U⊆ disjoint W)(hC:IsCompact U)
include hC
omit [LinearOrder W] in
lemma upper : ∃ R:ℝ, 0<R∧∀ y∈U, ‖y‖≤ R:= by obtain ⟨c,hc⟩:= hC.exists_bound_of_continuousOn (f:= id) continuous_id.continuousOn; exact ⟨ max 1 c,lt_max_of_lt_left zero_lt_one,fun _ he=> (hc _ he).trans (le_max_right ..) ⟩
include hp
omit [LinearOrder W] [Fintype W] in
lemma under (x y:W)(h:x ≠ y):∃ e:ℝ,0<e∧∀ p∈U,e≤ ‖p x-p y‖:= by
    rcases U.eq_empty_or_nonempty with hu|hu; · subst U; exact ⟨ 1,by norm_num, by simp ⟩
    let f(p:W→ Tone.QP):= ‖p x-p y‖; obtain ⟨p,hp',ht⟩:= hC.exists_isMinOn hu (f:=f) (by unfold f; fun_prop); exact ⟨ _, ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( (show Injective p from hp hp').ne h ) ) : 0< f p ), fun _ h=> ht h⟩

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
include hq
lemma admission : Dial.Uses ρ l μ:= by
    apply warm _ hq μ Index.i (l) Index.c Index.daily tendsto_comap
    · intro w; obtain ⟨R,hR,hK⟩:= upper hC; refine ⟨ R,hR,fun i=>?_⟩; let s:=clock q i.i; let p:=site q i.i i.d; change ‖Tone.embed ( i.d w )‖≤ R*Real.exp s; rw [ ← div_le_iff₀ (Real.exp_pos s) ]; let q':= Tone.embed (i.d w); have hx : ‖( p w )‖≤ R:= le_trans (norm_le_pi_norm ..) (hK _ i.alive); change ‖Real.exp (-s) • q'‖≤_ at hx; rw [ norm_smul_of_nonneg (Real.exp_pos _).le, Real.exp_neg ] at hx; rw [div_eq_mul_inv, mul_comm]; exact hx
    obtain ⟨R,hR,hK⟩:=upper hC; apply Dial.unpose (v:=μ); intro i j H
    obtain ⟨ r,hr,ht⟩:= under hp hC i j H; refine ⟨ ⟨ 2*R,by positivity,fun k=>?_⟩,⟨ r,hr,fun k=>?_⟩ ⟩ <;> simp only [ Geo.roots, Real.exp_zero, Pi.zero_apply, Pi.sub_apply,mul_one ]; · change ‖site _ k.i k.d i-site _ k.i k.d j‖ ≤ _; rw [two_mul]; exact ((norm_sub_le ..)|>.trans (add_le_add ((norm_le_pi_norm ..)|>.trans (hK _ k.alive)) ((norm_le_pi_norm ..)|>.trans ( hK _ k.alive))))
    exact ht (site q _ k.d) k.alive
include B0
-- comparison rate for ordinary (and can use cumulant equivalent from Matched.accuracy)
theorem power (s:Finset W)(n:ℕ) : ∃ C:ℝ,0<C∧∃ m:ℕ,∀ j≥m,∀ a:Lattice.Cover,Daily q j a→∀ d:W→Lattice.Cover,site q j d∈U→
    dist (markedPrice φ A μ w ((ℶ) j) (clock q j) a d s n) (Dial.tour b w μ (site q j d) s n ) ≤ C*Real.exp (-mildG*(clock q j)):= by
    obtain ⟨C,h,H⟩:= (accuracy b φ ρ A μ w l B0 (admission q hq μ hp hC) s n |>.2).2; obtain ⟨m,hm⟩:= eventually_atTop.mp ( eventually_comap.mp H ); refine ⟨ C,h,m,fun j hj a hA d hd=>?_⟩; rw [ dist_eq_norm ]; exact hm j hj ⟨ j,a,d,hA,hd⟩ rfl -- ramp rfl

omit B0 hq hp hC [LinearOrder W] in
lemma open_disjoint : IsOpen ( disjoint W ) := by
    let Q:=( {x:W×W | x.1 ≠ x.2} ); rw [show disjoint W=⋂ i:Q,{x: Place W| x i.val.1≠x i.val.2} from ?_]; rotate_left
    · ext v; simp only [ disjoint, Set.mem_iInter, Set.mem_setOf_eq ]; exact ⟨ fun h i=> h.ne i.property,fun h i j hx=> Classical.byContradiction fun he=> ( h (⟨(i,j),he⟩:Q) ) hx ⟩
    exact isOpen_iInter_of_finite fun i=> isOpen_ne_fun (continuous_apply _) (continuous_apply _)

abbrev priceAt (i:ℕ)(a:Lattice.Cover)(x: Place W)(s:Finset W) := markedPrice φ A μ w ((ℶ) i) (clock q i) a (Tiles.mesh (clock q i) ∘ x) s

theorem moves (s:Finset W)(n:ℕ){ε:ℝ}(he:0<ε): ∀ᶠ i in atTop, ∀ a:Lattice.Cover, Daily q i a →∀ x∈U,dist (priceAt φ q A μ w i a x s n) ( Dial.tour b w μ x s n ) < ε:= by
     let ζ(i:ℕ) := Real.exp (-(clock q i)); let Cx(x:W→Tone.QP):= Dial.tour b w μ x s n; obtain ⟨δ,hd,hD⟩:= hC.exists_cthickening_subset_open (open_disjoint (W:=W)) hp; let C:=cthickening δ U; have hcp : IsCompact C:=hC.cthickening; let gc i (x:Place W):= site q i (Tiles.mesh (clock q i) ∘ x)
     have hx(i:ℕ)(x:Place W): dist (gc i x) x≤ζ i:= by rw [dist_eq_norm]; exact ( pi_norm_le_iff_of_nonneg (by unfold ζ; positivity)).mpr fun w=> unmesh _ _
     obtain ht: Tendsto ζ atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (forward q hq)); obtain hu:= Real.tendsto_exp_atBot.comp ((forward q hq)|>.const_mul_atTop_of_neg (neg_lt_zero.mpr mild_p )); obtain ⟨c,h,h0,B⟩:= power b φ q hq A μ B0 w hD hcp s n -- order variables
     obtain ⟨u,hh,hx'⟩:= Metric.uniformContinuousOn_iff.mp ( hcp.uniformContinuousOn_of_continuous (f:=Cx) (fun x hx=> (Dial.contin b w x (hD hx) s n μ |>.1).continuousWithinAt )) (ε/2) (half_pos he)
     filter_upwards [eventually_ge_atTop h0, ht.eventually ( gt_mem_nhds hd ),ht.eventually ( gt_mem_nhds hh ), hu.eventually (gt_mem_nhds (show 0< ε/2/c from div_pos (half_pos he) h)) ] with i hi hxδ htop hxμ a ha x hv; have HM : gc i x ∈ C:= closedBall_subset_cthickening hv δ (( hx i x ).trans (show ζ i<δ from hxδ).le); apply lt_of_le_of_lt (dist_triangle _ ( Cx ( gc i x )) _)
     have ht': c * Real.exp ( -mildG * (clock q i)) < ε/2:= (mul_comm (Real.exp _) c) ▸ ( ( lt_div_iff₀ h ).mp (show Real.exp ( -mildG * (clock q i) ) < ε/2/c from hxμ)) -- -- typecast via function
     rw [← add_halves ε]; exact add_lt_add ((B _ hi a ha _ HM).trans_lt ht') (hx' _ HM x (closedBall_subset_cthickening hv δ (Metric.mem_closedBall_self hd.le)) ((hx i x).trans_lt htop))
end YM.FVA2.CompactRate
