import YM.QuadraticLocal.Rough.Rove
import YM.QuadraticLocal.Deletion.Crop
/-!
 # S2. Commutation theorem for the true vacuum merger
 (`Port_Refrain` factors). Compare polynomial with some inserted input terms
 carrying preserved historical discrepancy values CLEAN (e_old,Glyph). Since
 want to pay also sharp qelt without multiplying a formation-phase gate by
 the inflated-error factor when leaving along the untainted marks, construct
 a proof of price on a different input polity `T'`, in all REAL Sector stamp,
 require same H prototype, Θ mission etc. Need identity *before final*
 assembly shifts for re-expression, so that we can pay these with the same
 Ψ footprint.Education.Instance.H_Work.En.Counter.Description.
 This file verifies raw Lit portion. Uses S: `Sector.Expression.Student.step
 Travel.raw` post-predicted based on current ℒ.N.Selector.`.
 Does not authorize a log estimate from equality of marked Density!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Season.Duet
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)


variable (N:ι→Lotus.Leaf R)
-- compare through step even if weights differ. Supports costs sorted same.En.Header.Parameter.Profile
variable {V:Type*}{X:Coat T F} (p:Drums M S) (q':Drums N S)
local notation "mp"=> team M p
local notation "np"=> team N q'
variable (he : p.val=q'.val)(hp:∀ i∈p.val,(M i).turn=(N i).turn)(hF:∀ i∈p.val,(M i).ingredient=(N i).ingredient)
include he hp hF
lemma marks : (team M p).signs S=(team N q').signs S:=by
    rw [Palette.label, Palette.label]; unfold Tickets.reach; rw [← he]; refine Finset.image_congr (fun i hi=>congr_arg (·.badge S) (hp i hi)) -- maybe not library
lemma rounds (a:ℝ)(z:Directions G f): (mp).paidU X a z=(np).paidU X a z:=by
    unfold Team.paidU; rw [Solos.shape M p (fun x=>x.paidU X a z),Solos.shape N q' (fun x=>x.paidU X a z),← he]; refine prod_congr rfl fun i hi=>?_ ; unfold Leaf.paidU Leaf.fond; rw [hF i hi,hp i hi]
lemma premium (l:Finset ℕ)(d:Molecule S) (z:F.Slice G × Air f G): (mp).into X W o.a Q.table l Q.halo d z=(np).into X W o.a Q.table l Q.halo d z:=by
    unfold Team.into Team.premium; rw [marks M N p q' he hp hF, rounds M N p q' he hp hF]
lemma thirst (X:Coat T F) (l:Finset ℕ)(d:Molecule S): (mp).tithe X l W o.a Q.table Q.halo d=(np).tithe X l W o.a Q.table Q.halo d:=by
    unfold Team.tithe; simp_rw [premium M N p q' he hp hF l d]
lemma alpha (V:Config G c)(d:Molecule S): Palette.act M H χ V d p=Palette.act N H χ V d q':=by
    unfold Palette.act Team.lotus likely; refine congr_arg ( (_:ℝ)*·) (Finset.sum_congr rfl (fun j _=>?_)) -- orientation likely
    unfold Team.bloom; dsimp only; split; next h=> unfold Team.steep likely; refine congr_arg ( (_:ℝ)* ·) (Finset.sum_congr rfl (fun i _=>Duet.thirst M N p q' he hp hF _ _ _ ))
    next=> rfl
omit he hp hF
-- compare whenever ℓ output pure. Uses Lyric.scripted (non-differentiated), no support obstruction from out-of-mask changes. Orientation in formula.We. Need both Frames for future obligations.
variable {κ K Y γ V0 T0:ℝ}
variable (U:Pad H j χ) ( W : H.fragrances ) ( u:Syllable M H W )( v:Syllable N H W ) (z:ι→ℝ)
variable (hT:∀ i,(u i).val=(v i).val)
local notation "F₁"=> ( Mosaic.jewel M H χ W u )
local notation "F₂"=> (Mosaic.jewel N H χ W v)
include hT
lemma score : (F₁).letters=(F₂).letters:= by refine Finset.sum_congr (g:=fun i=>(Mosaic.tile N H χ (W.2 i).val (v i)).letters) (rfl : (univ:Finset (Option (Fin W.1)))=univ) ?_; exact fun i _=>congr_arg Finset.val (hT i)
variable {Hw :Type}[DecidableEq Hw]{Rm:Marker.Census Hw}
variable (hs:∀ i∈ ( Mosaic.jewel M H χ W u ).letters, (M i).turn=(N i).turn)
    (hf:∀ i∈ ( Mosaic.jewel M H χ W u ).letters,(M i).ingredient=(N i).ingredient)
include hs hf U
set_option maxHeartbeats 600000
lemma homogeneous (X:Config G c) : (F₁).emit z X= (F₂).emit z X:=by
   unfold Verse.emit Verse.stock; rw [ score M H χ N W u v hT ]; apply congr_arg ( HMul.hMul _ ); change Lyric.cut M H χ W u X=Lyric.cut N H χ W v X; rw [← Lyric.scripted M H χ W u U.S.N X,← Lyric.scripted N H χ W v U.S.N X]; apply congr_arg ( HMul.hMul _ ); apply prod_congr rfl; intro p hp; have hv (i:ι)(he:i∈(u p).val): i∈(F₁).letters := Mosaic.holds Finset.univ (fun i=>( Mosaic.tile M H χ (W.2 i).val (u i) ).letters) i |>.2 ⟨p,mem_univ p, he⟩; exact Duet.alpha M H χ N _ _ (hT p) (fun i hi=> hs i (hv i hi)) (fun i hi=> hf i (hv i hi)) X _ -- order
omit hs hf U
-- Reconstruct at subst.M.Policy witnessed in concrete stamping.Ctty.H.Layout
variable (Sx:Set Hw)(ξ:ι→ Marker.Poly Rm)
variable (hV:∀ i∈( Mosaic.jewel M H χ W u ).letters, YM.QuadraticLocal.Deletion.crop Rm Sx (ξ i)≠0→ (M i).turn=(N i).turn ∧ (M i).ingredient=(N i).ingredient)
local notation "Ψ"=> YM.QuadraticLocal.Deletion.crop Rm Sx
include hV U
variable (θ' : Finset ℕ) -- scratch
local notation "z₀"=> (Set.univ:Set ι)
omit U hT hV in
private lemma rumors {p:Multiset ι} {i:ι}(h:i∈p)(hz:Ψ (ξ i)=0): Ψ (Verse.controls Set.univ ξ p)=0:= by
   have H := map_multiset_prod (YM.QuadraticLocal.ModeWeight.alg Rm (fun i=> if i∈Sx then 1 else 0)) (p.map ξ) ; unfold Verse.controls; simp only [Set.mem_univ, ↓reduceIte, id_eq]; rw [show Ψ (( p.map ξ ).prod)=_ from H]; exact Multiset.prod_eq_zero (hz ▸ (Multiset.mem_map_of_mem _ (Multiset.mem_map_of_mem ξ h)))
lemma continuity (V: Config G c): (YM.QuadraticLocal.Deletion.crop Rm Sx) ((F₁).paint Set.univ z ξ V)=(YM.QuadraticLocal.Deletion.crop Rm Sx) ((F₂).paint Set.univ z ξ V):=by
   unfold Verse.paint; rw [(Ψ).map_smul,(Ψ).map_smul,← score M H χ N W u v hT]; by_cases h: Ψ (Verse.controls Set.univ ξ (F₁).letters)=0; rw [h,smul_zero, smul_zero]; have hp i (he:i∈(F₁).letters):= hV i he (fun hx=> h (rumors _ _ he hx)); rw [Duet.homogeneous M H χ N U W u v z hT (fun i hi=>(hp i hi).1) (fun i hi=>(hp i hi).2)]
end YM.RemainderComparison.Season.Duet
