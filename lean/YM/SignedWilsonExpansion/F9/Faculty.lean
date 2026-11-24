import YM.SignedWilsonExpansion.F9.Roke
import YM.SignedWilsonExpansion.F9.Porter
import YM.SignedWilsonExpansion.F9.ComposedP
/-!
# Acquiring a commissioned test: financial assembly on the estimator map

This step is before Physical application. Keeps powered estimates in cost even where the L price
will later enter a small-r regular coefficient. Converted *bare to ℓ* on real spins.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
namespace YM.SignedWilsonExpansion.Commission.Method
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes Jury Reg
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa
open Stair Tape RateQ
variable {G:Gauge}{n d k e j:ℕ} {ι:Type} {L:Filter ι}{q:ι→ℝ}
variable (h:G.Simple)(T:MS_Data G (Position.OpenAxis.Plot (FVA2.Press.portDeck G)))(S:Prescription ( FVA2.Press.portDeck G)) (W:Initialize G){P':Normalize.Store G}(K:Rose.Pick P') (M:Scale.System.Contract W K T S)
local notation "Q'"=> (Query.crew h T S W K M)
abbrev StaffG (G:Gauge)(d:ℕ) := Tape (Labels.Label G d→ₗ[ℂ]Sec G d)
abbrev magazine (G:Gauge)(d:ℕ):= (x:Query) → Tape.Table (Sec G d) x.1
-- reach all queries in fixed room. crew actual READS only.P' covers witnesses outside too.
def memoir (W:Initialize G)(K: Rose.Pick P')(d:ℕ) (Y:ι→ magazine G d): Prop:= ∀ (i: Query) k (t:Tags G d i.1), Tendsto (fun v=> Y v i k t) L (𝓝 (Query.listK i (Measure.start W K d) k t)) -- L implicit but bind explicit not auto? G implied
-- Width buys freezes station.W.C.O height d
structure Faculty (W:Initialize G)(K: Rose.Pick P')(F:Labels.Frame G d) (x:ι→StaffG G d)(z:ι→InkQ)(Y:ι→ magazine G d)(L:Filter ι)(q:ι→ℝ)(a: Finset Query)(k:ℕ) : Prop where
    param : ∀ i, constantCoeff (z i)=0
    natural : ∀ i, realInk (z i)
    blessed (i:ι) (j:ℕ) : Trustee (x i j) (if j=0 then 1 else 0)
    reads : memoir W K d Y (L:=L)
    allowed : Maxer L q
    pace (i:Query)(p:i∈a)(v:Fin i.1→ F.Index) : Costy L q (fun j=> exam (Tape.composed (Y j i) (z j)) (fun _=> x j) (F.basis ∘ v)) k
namespace Faculty
variable {W K h T S} {a:Finset Query}{F:Labels.Frame G d}{U:ι→ StaffG G d}{z:ι→ InkQ}{Y:ι→magazine G d}
variable (P:Faculty W K F U z Y L q a k)
include P
lemma floors (i:Query)(v:i∈a)(u:ι→ Fin i.1→ Labels.Label G d)(Q:∀ i':Fin i.1,Across L q ℂ (fun j=>u j i')): Costy L q (fun j=> exam (Tape.composed (Y j i) (z j)) (fun _=> U j) (u j)) k:=
   fun n h=> keeps P.allowed F.basis _ _ n u Q fun f=> P.pace i v f n h
include M h
lemma hook (a':Axis) (u:Tags G d 2): Tendsto (fun j=> Y j (Query.anchor a') 0 u) L (𝓝 (scene (Gram.nodes a') d u)):=by
    have ht:= P.reads ( Query.anchor a' ) 0 u; change Tendsto _ _ (𝓝 ((Equator.iris (G:=G) (Query.anchor a').2) u)); rw [← orderd0 h T S W K M (d:=d) 2 (Query.anchor a').2]; exact ht
lemma firstQ (a':Axis)(p':Query.anchor a'∈ a): Across L q ℂ (fun i=> U i 0):=by
    apply Across.actEnough P.allowed F.basis; intro b; let x:=F.basis b; let X(i):= U i 0 x; let I:= Query.anchor a'; let A(i:ι): XSpace.Structure1.Point G d 2:= Y i I 0; let Q:= Module.finBasis ℂ (Sec G d)
    let p:=![x, Labels.tensor (Signed.mirror a').ortho (Labels.realBar x)]; let B(i):= A i ![X i,Gram.flipE a' (X i)]; have ht: Billed L q B:=by
       let u:=P.floors I p' (fun _=> p) (fun j=> Across.solid _); apply Billed.via ( u 0 ( Nat.zero_le k ) ); filter_upwards with i; rw [exam,heel _ ( P.param i )]; apply Eq.symm; apply congr_arg (A i); ext1 v; fin_cases v
       · rfl
       change U i 0 (Labels.tensor _ (Labels.realBar x))= _; unfold Gram.flipE; rw [(P.blessed i 0).2.2.2 (Signed.mirror a'), (P.blessed i 0).2.2.1]; rfl
    obtain ⟨k',hk,H⟩:= Gram.house L a' Q A (fun i j=> P.hook (h:=h) M a' _); apply Across.basisN P.allowed Q; exact Billed.square P.allowed _ k' ht hk (H.mono fun i h=> (h (X i) ).trans (Complex.re_le_norm (B i)))
end Faculty
-- pack β budgets from Porter. Need prove affolder.Head from q.meets.Desire lands via ground poly. helper conceptual.Scales.Provides rooms.
end YM.SignedWilsonExpansion.Commission.Method
