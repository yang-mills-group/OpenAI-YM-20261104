import YM.FVA2.PoesyL
import YM.FVA2.MarkersBasis
/-!
# Derivative of pinned branch. Translation-covariant derivative accounts for root changes

 Along a single moving source. Extend iterated. Purpose rate.
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real Metric
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane MS.Dial MS.Wind MS.High MS.Fiddle Wire Belt Finset
open scoped BigOperators ContDiff Classical
variable {G: Gauge} {I W: Type} [LinearOrder W] {v:ℝ}
variable {A: Deck G}{B:Booked A}{S:MS_Data G B}
variable {x: Position W ℝ}{U V: Rake.Dance G ℝ W}{a: W→Choice v S}
variable (h:Mesh (frameF ℝ v) x)(hu:Frozen a U x) 
variable (g: W) (d:QP)
local notation "Υ"=> frameF ℝ v
local notation "Δ"=> constantP G ℝ (PlanetD G)
variable (hv:Frozen ( awaken g a d ) V x)
variable {Z: Set ℝ}(H:IsOpen Z)
variable (hA:PathAlong g d x Z)
variable {w y: Finset W}
local notation "Ψ"=> field (Landau.parity (A:=Axis) (C:=G.ColorIndex))
section smooth
variable [Fintype W] (a: W→Choice v S)(g:W→QP)
def vicinity (W:Type) : Set (W→QP):= setOf Injective
lemma airT (W:Type)[LinearOrder W][Fintype W]: IsOpen (vicinity W):= by
    apply isOpen_iff_mem_nhds.mpr; intro x h; apply Eventually.mono (earlyW h); intro i v; let A(w:W):= Dial.Window w x; have hm: pointI A i=i:= funext fun j=> if_pos v; exact hm ▸ detailI 0 ( turnH h 0 ) i
lemma payable (hp:g∈vicinity W)(w:Finset W)(p:ℕ) : ∃ r:ℝ,0<r∧∀ᶠ x in 𝓝 g,‖priceZ a x w p‖ ≤ r:= by
    let Z(i:W):= Dial.Window i g; have h:= turnH hp v; let K:= frameF (W→QP) v; obtain ⟨U,hU⟩:= footing a h;
    obtain H|H:= w.eq_empty_or_nonempty; · subst w; refine ⟨1, zero_lt_one,?_⟩; filter_upwards [ (airT W).mem_nhds hp ] with x h; rw [ priceZ,(choiceFox a h).1 ]; simp only [ Pi.zero_apply, show blade (0:Glade G Unit) ()= 0 from ( Fleet.allow_zero _).2,norm_zero ]; norm_num
    obtain ⟨C,hC,k,hV⟩:= walletCast a h hU H p|>.2.2; let r:= C*(moneyX K 0 ( Vane.charge (Choice.order∘a) w ) k g ); refine ⟨ r+1, ?_,?_ ⟩; · nlinarith [show ‖blade (U w p) g‖ ≤ r from hV _, norm_nonneg (blade (U w p) g )]
    filter_upwards [earlyW hp] with i hi; rw [ show priceZ a i w p= _ from ( congr_arg ( fun x:W→QP=> priceZ a x w p ) ( show i=pointI Z i from funext fun j=> Eq.symm ( if_pos hi ) ) ).trans ( solveZ a h hU i w p|>.symm ) ]; apply le_trans ( hV i ) ( le_trans (b:=r) le_rfl ?_ ); linarith
abbrev Vary (W:Type):= Sigma fun _:W=> Axis
def headB (W:Type)[Fintype W]:Module.Basis (Vary W) ℝ (W→QP):= Pi.basis (fun _:W=>Pi.basisFun ℝ Axis) -- infer.
variable (w: Finset W)(p:ℕ) -- g implicitly explicit
abbrev look (p:Axis):QP:= Pi.basisFun ℝ Axis p
def rent (i: Vary W) :ℂ:= liftP w i.1 * priceZ (awaken i.1 a ( look i.2 )) g w p -- args inspect
lemma ex (i:Vary W)(hp:g∈vicinity W): HasLineDerivAt ℝ (fun x=>priceZ a x w p) (rent a g w p i) g ( headB W i ) := by unfold headB; rw [ Pi.basis_apply ]; exact alongC _ _ _ _ _ hp _
lemma ok (hp:g∈vicinity W): ContinuousAt ( fun x=>priceZ a x w p ) g := by
    choose r hr h using fun (i: Vary W )=> payable ( awaken i.1 a (look i.2)) g hp w p; let C:= ∑ i:Vary W, r i; refine Rails.continuity (headB W) (F':=fun p' x=>rent a x w p p') ?_ ( show 0 ≤ C from Finset.sum_nonneg fun i _=> ( hr i ).le );
    filter_upwards [eventually_all.mpr h,(airT W).mem_nhds hp] with i hi he; intro j; refine ⟨ ex a i w p j he,?_ ⟩; refine le_trans ( show ‖rent a i w p j‖ ≤ r j from ?_) ( Finset.single_le_sum ( f:=r ) (fun i _=> (hr i ).le ) ( mem_univ _ ) ); unfold rent liftP; split; · rw [one_mul]; exact hi j
    rw [zero_mul,norm_zero]; exact ( hr j ).le
-- use clm whole basis.Interlacing proofs
abbrev markB (W:Type)[Fintype W]: (Vary W→ℂ)→L[ℝ]( (W→QP) →L[ℝ] ℂ ) := LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp ( ( headB W ).constr ℝ ).toLinearMap ) -- universe
lemma examined (hp:g∈vicinity W): HasFDerivAt (fun x=>priceZ a x w p) (markB W (rent a g w p)) g := by
    apply Rails.deduct (headB W) (airT W) hp (F':=fun i g=>rent a g w p i); · intro i; simp
    · exact fun y h i=> ex a y w p i h
    intro i; unfold rent; exact ( ok _ g w p hp ).const_mul _
theorem profound : ContDiffOn ℝ ∞ (fun x=>priceZ a x w p) (vicinity W) := by
    apply contDiffOn_infty.mpr; intro n; induction n generalizing a with
    | zero=> simpa only [Nat.cast_zero, contDiffOn_zero] using ( show ContinuousOn _ _ from fun x hx=> (ok a x w p hx).continuousWithinAt )
    | succ n ih=> rw [ Nat.cast_succ ]; apply ( contDiffOn_succ_iff_fderiv_of_isOpen ( airT W ) ).2; refine ⟨ fun x hx=> (examined a x w p hx).hasFDerivWithinAt.differentiableWithinAt, fun h=>by simp at h,(show ContDiffOn ℝ ( n:WithTop ℕ∞ ) (fun x=> markB W (rent a x w p)) ( vicinity W ) from ContDiff.comp_contDiffOn (markB W).contDiff ?_ ).congr (fun i hi=> ( examined a i w p hi ).fderiv)⟩; apply contDiffOn_pi.mpr; intro x; unfold rent; exact contDiffOn_const.mul ( ih _ )
-- particular endpoint.
lemma sparkSmooth (g:W→Label A)(v:ℝ): ContDiffOn ℝ ∞ (fun x=> book S g v x w p) ( vicinity W ) := by
    let a:= choice v S ∘ g; refine ( profound a w p ).congr ( fun x hx=> ?_ ); let Z:= fox a x; unfold book priceZ; rw [ perfect (pin ( x:=x ) S g v hx) ( of_choice.mp ( choiceFox a hx ) ) ] -- syntax
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors MS.Puff.SplitP
-- spread.
abbrev Views (g:(W→QP)→ Finset W→ T ℂ): Prop:= ∀ i t, ContDiffOn ℝ ∞ (fun x=>g x i t) ( vicinity W )
lemma product {x y:( W→QP )→ Finset W→ T ℂ}(hx: Views x)(hy:Views y): Views (fun i=>(Trunk.stack (marked W)).core (x i) (y i)):= by
    intro i u; change ContDiffOn ℝ ∞ (fun p=>( ∑ t∈ subs i,Trunk.core ( x p t.1 ) ( y p t.2 )) u ) _; simp_rw [ Finset.sum_apply ]; apply ContDiffOn.sum; intro t _; refine ContDiffOn.sum (s:=Finset.antidiagonal u) (fun (j:ℕ×ℕ) _=> (hx t.fst j.fst).mul (hy t.snd j.snd))
lemma bright_power {x: ( W→QP )→ Finset W→ T ℂ}(hx:Views x) (s:ℕ): Views ( fun t=> ( Trunk.stack (marked W) ).power ( x t ) s ):= by induction s with| zero=> exact fun _ _=> contDiffOn_const| succ n ih=> exact product hx ih
lemma bouquet_spark {x: ( W→QP )→ Finset W→ T ℂ}(hx:Views x) : Views ( fun t=> bouquet ( x t ) ):= fun i u => by unfold bouquet Cheer Actors.cheers; simp_rw [ Finset.sum_apply ]; apply ContDiffOn.sum; intro i _; exact (bright_power hx i _ u).const_smul ( Actors.phase i ) -- smul ℂ
/-- **Smooth continuum** MS correlation kernels (include all inserted fields and order towers).
 Here no test derivatives on insertions are postulated; Separated points. -/
theorem tourSmooth (g:W→Label A)(v:ℝ): ContDiffOn ℝ ∞ (fun x=> tour S g v x w p) ( vicinity W ):= bouquet_spark (fun i q=> sparkSmooth ( S:=S ) i q g v ) w p
end smooth
end YM.FVA2.Poesy
