import YM.FVA2.Arrival.Landing
import YM.FVA2.Full.Images
/-!
# Unmarked analytic-frame BV comparison and the cost of undoing the source change

Using the supplied Echo+Vista Fourier proof, not assuming vanishing of the surviving constant
ghost-B terms or estimating individual $E_{t,Z}$. The two CCOrb's bracket
the undo over FULL marked sets: on the cover use `Echo` to get eventual equality from the
Weightless property along the marked shift; to bound the residual on the orbit use both sets of
Fourier image estimates (only bulk tuning needed). So this alternative proof demonstrates
quantitative regulator smallness of the effect on *readings*, not of each of the generators.
Does NOT set the source generators' contribution to zero at a fixed finite period. The first
unmarked canonical substitution, in contrast, **is** exact (including with marks when the
arguments are also substituted). Terminal result `Undo.quotient_rate`.

In this library the differentiated estimates of `SpaceOut.Images` are in the thermal
momentum-kernel norms: `Vista.ΔMark`, `WarpHere/HandC`/etc retain the $b=false/true$ rank
specs of the heat evolution (before sending evaluator length to infinity, incl cutoff difference
in `Mid`). See `quotient_rate` for the residual on cumulants, and `Removal/Platter` e.g. for the
full estimate; for the comparison out to any fixed order see `Landing.life`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Puff Puff.Actors Puff.Engine Puff.Mom
open SpaceOut Swirl Swirl.Near
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{i:I}{L:I→Side}{x:I→ Lattice.Cover}{p:Team} {V U: W→Actor G} {b: Bool} {η:I→ℝ} (c:Berth ( W:=W ) ( I:=I )) (i:I){s: Finset W} {Z:ℕ→ℂ}
-- literal equivalence for any i with half-period. replicate κglyph for lemma equival.
set_option quotPrecheck false
local notation "A"=> dimT L i
local notation "M"=> Master G (dimT L i) b
lemma canonical_in_advance (hp: Badge U)(h: Changes V U p) : PhysicalSum G p (η i) A b s (fun w=>c w i) ( x i ) U Z ↔ Endμ M σbranch ( NRG p (η i) ( dimT L i ) G b ) ( Font σbranch (ΓM c L i η x V) s ) Z:= by
   have hz : ( pay b • flatH G A )= SendB G A b ( core G 0 ):= rfl; obtain h0:= sendEven ( b:=b ) ( N:=A ) ( crisp G 0 ); obtain ht:= memBill ( b:=b ) ( N:=A ) ( crisp G 0 ) ( participates G 0 ); rw [ ← hz ] at h0 ht
   obtain ⟨hV,hg⟩:= powerfee ( G:=G ) ( b:=b ) ( N:=A ) ( Stripped p ) ( η i ); rw [ βalign, Near.translate c i h ]; exact ready_η ( zeroM b ) (paySym b) ( feeDown p ( η i ) ) (excavate G A p ( η i )) ( guise p (η i)) ht h0 μτrank hg hV ( τ_nil .. ) ( momentΓ c i U x η L hp (s:=s) )
end YM.MS.Fleet
namespace YM.FVA2.Arrival.Undo
open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.High MS.Koszul MS.Plane MS.Landau MS.Tone Lattice MS.Land MS.Tide MS.Latch MS.Heat MS.Book MS.Book.Convolve Program
open Native Wilsonian MS.Wind MS.Rake MS.Rake.Geo MS.Vista MS.Vane MS.City MS.Orbit Cog MS.Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom MS.Echo
open MS.Fleet MS.Swirl MS.Swirl.Near MS.Menus
open scoped Topology ContDiff Interval
variable {W I:Type}[LinearOrder W] {G:Gauge} (Y:XSpace.Initialize G)
variable (u : W→Label (Press.portDeck G))(A:Land.Prescription (Press.portDeck G))
local notation "p"=> A.team
local notation "φ"=> Press.wickInput Y
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "Xr"=> PortEntryF φ A ∘ u
-- exact equivalence, no-bulk tuning required, all finite periods half etc already exact.
variable (i: Lattice.Side)(x:Lattice.Cover)(v:ℝ)(c:W→Lattice.Cover)(s:Finset W)
set_option quotPrecheck false
lemma exact_canonical {f:ℕ→ℂ}: Top.value Y u A x c (periodN i) v s = f ↔ Endμ ( Master G (periodN i) true ) σbranch ( NRG A.team v ( periodN i ) G true ) ( Font σbranch ( Marks Yr v (periodN i) x c ) s ) f:= by
    let h:Even (periodN i).val:= ⟨ i.val,two_mul (α:=ℕ) i.val⟩; refine Iff.trans eq_comm ( Iff.trans ( Top.identifies Y u A x c (periodN i) v s h ).symm ?_ );
    have hu:Badge Ur:= fun _=> billRentF ..; have hx: Swirl.Near.Changes Yr Ur A.team:= fun w x=> rankVF ..;
    exact canonical_in_advance ( x:=fun (_:Unit)=>x ) ( η:=fun (_:Unit)=>v ) ( «L»:=fun (_:Unit)=>i ) ( «p»:=A.team ) ( b:=true ) ( s:=s ) ( Z:=f ) (fun i _=>c i) () hu hx
-- same coefficient along any Trial, comparing source-adjusted preamble/pay
variable (l:Filter I) (T:Dial.Trial I W)
local notation "L"=> T.side
local notation "μ"=> T.profile.η -- no char scale distinction! v above with Uses
local notation "Ψ"=> goalsK T.off T.profile.η Yr
local notation "Q"=> goalsK T.off T.profile.η (PortEntryF φ A ∘ u)
variable {K:Land.Booked (Press.portDeck G)}(S: MS_Data G K)(h:TaylorOKF S (Press.wickInput Y) A)(ht: Dial.Uses T l v)(hg:G.Simple)
-- Heat proof alternatives yield quantitative bounds.
-- (here using the specific geometry in `Uses`).
include h ht hg
theorem quotient_rate : ∃ (C:Vista.Visa I)(f z:Terrify W I), NearPlan l T.profile C T.side v ∧ CCOrb G μ p T.head L Ψ true f ∧ CCOrb G μ p T.head L Q true z ∧
    (f ∅=0∧ z ∅=0) ∧ (∀ i s, bury i s f= Top.value Y u A ( T.head i ) (fun w=>T.off w i) (dimT L i) ( μ i ) s ∧ Endμ ( Master G (dimT L i) true ) σbranch ( NRG p (μ i) ( dimT L i ) G true ) ( Font σbranch ( ΓM T.off L i μ T.head Xr ) s ) ( bury i s z )) ∧
    (∃ Z V X D:Rake.Dance G I W, SpaceOut.Images G C L μ T.head Ψ p true Z V∧ SpaceOut.Images G C L μ T.head Q p true X D∧ (∀ s:Finset W,s.Nonempty→∀ k,f s k= toZ V s k ∧ z s k= toZ D s k ∧ cash_out C L ( f s k-toZ Z s k ) ∧ cash_out C L ( z s k-toZ X s k )) ∧ (∀ k s,toZ Z s k=ᶠ[l]toZ X s k)) ∧
    ∀ k s,∀ ρ:ℝ, PeakT l T.profile ρ ( fare (Label.h ∘ u) T.profile f s k-fare ( Label.h∘u ) T.profile z s k ):= by
    obtain ⟨V,hV,hP⟩:= qualifies T.off ht.total ht.reality ht.upright ht.super; obtain ⟨hK,hX,H,hmenu⟩:= billMenusF u ( «φ»:=φ ) ( A:=A ) hg;
    let L':= T.side; obtain ⟨X,F,f,hI,hF,hf,h0,hXU,_,hpay⟩:= imageBank ( P:=T.head ) h.bulk (show SpaceOut.FlowSet V Ψ from moneyM T.off hV fun i=>⟨ false,0,hK.badge i ⟩) hV.proper true ht.clear ht.wind; obtain ⟨Y',Z,z,hZ,hY,hz,he,hQ,_,hp⟩:= imageBank (P:=T.head) h.bulk (show SpaceOut.FlowSet V Q from moneyM T.off hV (fun i=> ⟨ false,0,hX.badge i ⟩)) hV.proper true ht.clear ht.wind;
    -- analogous Eventual-Echo identities used in `Tide`.
    let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let w i s n:= toZ F s n i; have HS(k:ℕ)(s:Finset W) : toZ F s k=ᶠ[l]toZ Z s k := Filter.EventuallyEq.symm ( Tide.peaks (l:=l) (X:=a) (Y:=w) ( marked W ) Toy ( pointed _ (zeroZ hY.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> MS.Echo.quote ( Tide.payTune T.off ht.knit ht.upright ) hX hK h.bulk hg hmenu hY hF n s) s k )
    refine ⟨ V,f,z,hP,hf,hz,⟨ h0,he⟩, fun i s=> ⟨ ( exact_canonical Y u A ( L i ) ( T.head i ) (μ i) (fun w=>T.off w i) s ).2 ?_ |>.symm, σPay T.off i hz hX.badge ⟩,⟨ F,X,Z,Y', hI,hZ,fun s h n=>⟨ (hpay s h n).1,( hp s h n ).1,( hpay s h n ).2,( hp s h n ).2 ⟩, HS ⟩,?_⟩
    · exact σPay T.off i hf hK.badge
    intro k s τ; by_cases hs:s.Nonempty; swap; · unfold fare; rw [Finset.not_nonempty_iff_eq_empty.mp hs,h0,he,sub_self]; exact PeakT.zero
    have hm:= Vista.cash_sub ( hpay s hs k |>.2 ) ( hp s hs k |>.2 ); unfold fare; rw [← mul_sub]; apply significant; refine PeakT.fromζ ( hP.costG hm _ ) ?_; filter_upwards [HS k s] with i hi; simp only [Pi.sub_apply,hi]; abel
end YM.FVA2.Arrival.Undo
