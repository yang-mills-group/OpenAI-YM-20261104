import YM.FVA2.Hearth.Reclose
import YM.FVA2.Arrival.Folio
/-!
# Full joint valuations with nonlinear covariantized input stencils

Use the `Initialize` and `Folio` slots. Fk here will be in the corresponding
native units; don't omit the external engineering factors in the position comparisons
(see `Handoff`, `Arrival`). Need the power-shift endorsement even before the final
payment (`prophecy` compares at *all* retained fields, not just the scalar there).

Use `toll` to finish the comparison to `Folio.coefficients`.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Arrival RGComparison.Core16 PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge} (Y:XSpace.Initialize G) {n:Side}
variable (i:Folio G)
local notation "O"=> Folio.placard Y i n
private def control (G:Gauge){n:Side}(h:Even n.val): Flats G n→L[ℝ] MS.Native.Chart.City G (Site n):= LinearMap.toContinuousLinearMap ((Pert.Orb.LinkP G n).subtype.comp (Orbit.fanEquiv (G:=G) h).symm.toLinearMap)
private lemma trueReading (h:Even n.val): seed O= Folio.placard Y i n ∘ MS.Native.Chart.nation ∘ (control G h):= by
 funext u; let p:= (Orbit.fanEquiv (G:=G) h).symm u; change O (Orbit.ignite u)=O (Pert.Orb.positiveLinks p); rw [← Orbit.lit p,show Orbit.touches G n p=u from (Orbit.fanEquiv h).apply_symm_apply u]
lemma represent (h:Even n.val): ∃ v:Ticket (Flats G n), imprintRoot O = X^(Folio.slots i)*v:= by
 let A:= Stack.rise (seed O); refine ⟨Stack.drop (Folio.slots i) A ,?_⟩; symm; apply Stack.recover (Folio.slots i) A
 intro j hj; unfold A Stack.rise; rw [PowerSeries.coeff_mk]; apply Subtype.ext; funext x; change jet (seed O) j x=0; rw [trueReading Y i h]; exact Change.Stencil.flowing (Folio.leaf Y i) i.addr j (Folio.currency Y i) hj (Flats G n) (control G h) x
-- entire product rank, before every possible Broadcast. prefer compact `.drop` once.
variable {L:Fabric G n}(T:Cloth L) (l:List (Folio G))
 def markValue (l: List (Folio G)) (n:Side) : Ticket (Flats G n):= Stack.drop (Folio.asset l) (imprintRoot (Folio.scenario Y n l))
lemma launching (ev:Even n.val) : X^(Folio.asset l)*markValue Y l n = imprintRoot (Folio.scenario Y n l):= by
 let p (l:List (Folio G)):= imprintRoot (Folio.scenario Y n l); change X^_ * Stack.drop _ (p l)=p l
 have h(l):∃ q:Ticket (Flats G n), X^(Folio.asset l)*q=p l:= by
    induction l with
    | nil=> refine ⟨1,?_⟩; change X^0 * _ = Stack.rise (1:Flats G n→ℝ); rw [pow_zero,one_mul,Stack.rise_one]
    | cons i l ih=>
       obtain ⟨A,hA⟩:= represent Y i ev; obtain ⟨B,hB⟩:= ih; refine ⟨A*B,?_⟩
       let a:= seed (Folio.placard Y i n); let b:= seed (Folio.scenario Y n l); change X^(Folio.slots i+Folio.asset l)*(A*B)= Stack.rise (a*b)
       let t:= localTruss (endcap (G:=G) n ev); rw [Stack.rise_mul (certified t _ (Folio.votes Y i n ev)) (certified t _ (Folio.matured Y n l ev)), show Stack.rise a=X^_*A from hA, show Stack.rise b=X^_* B from hB.symm,pow_add]; ring
 obtain ⟨q,hq⟩:=h l; rw [← hq, Stack.drop_mul]

variable (z:L.Accounts→PowerSeries ℝ) (H:∀ i,0<term (z i) 0){J:ChartRatio G}(hj:LocalRatio J)
local notation "V"=> Folio.scenario Y n l
local notation "F"=> Facade.drive T (z ∘ some) (headquarters z)
local notation "s"=> collared T z hj H

local notation "D" => Folio.asset l
local notation "q"=> markValue Y l n
lemma drive_x (k:ℕ)(A:Ticket (Flats G n)) : (F (X^k *A) J s).2 = X^k * (F A J s).2:= by
 rw [←follows T z H hj,← follows T z H hj A,map_mul,map_pow, show boost (line T) X=X from PowerSeries.map_X ..]; unfold sticker; rw [fitTake]

lemma broadcasted : X^D * (F q J s).2 = (F (imprintRoot V) J s).2 := by rw [←drive_x T z H hj D q, launching Y l L.even] -- implicit hj

lemma toll (h:z none=1): purchase T z H hj q= Folio.coefficients Y n l:= by
 unfold purchase; let N:= Folio.asset l
 have hp:X^N*(purchase T z H hj q)= purchase T z H hj (imprintRoot V):= by
      rw [←sold T z H hj,←sold T z H hj]; unfold tally current;
      rw [← broadcasted Y T l z H hj, map_mul (boost (castAt (finish T))), map_pow (boost (castAt (finish T))), show boost (castAt (finish T)) X=X from PowerSeries.map_X ..];
      rw [mul_left_comm (flat T z H hj 1) (X^D), Stack.taking,mul_assoc]
 rw [diagram T z H hj h (Folio.matured Y n l L.even),← Folio.external Y l L.even] at hp; exact mul_left_cancel₀ (pow_ne_zero N PowerSeries.X_ne_zero) hp
variable (x:G.ColorIndex)(y:Flats G (Bottom L)) (w:L.Accounts→ℝ→ℝ) (N:ℕ)
include hj H
-- through N, coefficient after transporting Laurent currency via same Art.Work. Explicit.
lemma prophecy (hw:∀ i,ContDiffAt ℝ ω (w i) 0)(h:∀i,Through N (amount (w i)) (z i)) (k:ℕ)(hi: (Folio.asset l)+k≤N):
 Lumen.Fk.read (localClimate T y x w) J (tease T x) (lens T y x (rad T V)) (Folio.asset l) k= coeff k (Stack.read y (F q J s).2):= by
 rw [predicted T y x w hj z H N hw h V (Folio.matured Y n l L.even) _ k hi, ← broadcasted Y T l z H hj,map_mul,map_pow, show Stack.read y X= X from PowerSeries.map_X .., PowerSeries.coeff_X_pow_mul', if_pos (by omega),Nat.add_sub_cancel_left]
-- no implicit mask.Style change.
end YM.FVA2.Hearth
