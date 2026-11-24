import YM.SignedWilsonExpansion.F9.Gram
import YM.SignedWilsonExpansion.F9.Glider
import YM.SignedWilsonExpansion.F9.Tangent
/-!
# The Commissioner gathers and heights of tangent samples over `Frames d`. FVA2 prescription fixed.

This is a family of *finite point lists*, finite cost via prior Stamp Ledger. Build it anew for
 each demanded height/order. Keeper:
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 370000
namespace YM.SignedWilsonExpansion.Commission.Method
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open FVA2 FVA2.Arrival FVA2.Main FVA2.Scale FVA2.Position FVA2.Position.Axes Jury Reg
open scoped Topology ContDiff BigOperators Classical
open WilsonCoeffUV.Mer.Xa
variable {G:Gauge}{n d k:ℕ} {ι:Type} {L:Filter ι}{q:ι→ℝ}
variable (h:G.Simple)(T:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(S:Prescription (Press.portDeck G))(W:Initialize G){P':Normalize.Store G}(K:Rose.Pick P') (M:Scale.System.Contract W K T S)
-- Requests. always all labels evaluations on these sites, not indicator at regulator data.
abbrev Query:= Σ n:ℕ, Stage n
local notation "Aᶠ"=> Measure.start W K d
namespace Query
def listK (p:Query)(A:Way G d): Tape.Table (Normalize.Sec G d) p.1:= A p.1 p.2
abbrev anchor (a:Axis): Query:= ⟨2,Gram.nodes a,Gram.nodes_conf a⟩
abbrev applies (p:Query)(A: Tape.Table (Normalize.Sec G d) p.1)(t:Tags G d p.1): TPoint G d→ₗ[ℝ] ℂ:=by
    refine { toFun:= earPoint A t, map_add':= fun x y=> ?_, map_smul':= fun c x=> ?_ }
    · change (( ( x.2+y.2:ℝ ):ℂ)*A 1 t + ∑ i,A 0 (update t i (( x.1+y.1 ).val (t i))))= _; unfold earPoint; simp only [Submodule.coe_add, LinearMap.add_apply,MultilinearMap.map_update_add, Finset.sum_add_distrib,Complex.ofReal_add, add_mul]; abel
    change ((( c*x.2:ℝ ):ℂ)* A 1 t+ ∑ i, A 0 (update t i ((c • x.1).val (t i))))= c • _; unfold earPoint; rw [smul_add, Complex.real_smul]; simp only [Submodule.coe_smul_of_tower, LinearMap.smul_apply, Finset.smul_sum, Complex.ofReal_mul, mul_assoc, ← @MultilinearMap.map_update_smul]; -- lemma submodule witness
    -- Ether. map_smul over ℝ rewrite Normalize.volumes
    congr 1; exact Finset.sum_congr rfl (fun i _=>by rw [show ∀ x:Normalize.Sec G d,c • x=(c:ℂ) • x from (fun x=> (IsScalarTower.algebraMap_smul ℂ c x ).symm), MultilinearMap.map_update_smul ]; exact IsScalarTower.algebraMap_smul ℂ c ((A 0) _) )
abbrev Sensor (G:Gauge)(d:ℕ):= Σ q:Query, Tags G d q.1
abbrev receives (P:Sensor G d) (Y: (q:Query)→Tape.Table (Sec G d) q.1): TPoint G d→ₗ[ℝ]ℂ:= applies P.1 (Y P.1) P.2
lemma hotel (d:ℕ)(A:Way G d)(B:∀ x:TPoint G d,(∀ n (p:Stage n)(t:Tags G d n),earPoint (A n p) t x=0) → x=0) : ∀ x:TPoint G d,(∀ i:Sensor G d, receives i (fun j=> listK j A) x=0) → x=0:=fun x h=> B x fun n p t=> h ⟨⟨n,p⟩,t⟩
abbrev resident (d:ℕ)(u:6≤d) : Finset (Sensor G d):= (Foundation.cuts _ (hotel d (Measure.start W K d) (independence h T S W K M u))).choose
abbrev crew (a:Axis)(d:ℕ)(u:6≤d): Finset Query:= insert (anchor a) ( (resident h T S W K M d u).image Sigma.fst )
lemma tangent_stock (Y:ι→ (x:Query)→ Tape.Table (Sec G d) x.1)(p:∀ (i:Query) (k:ℕ)(t:Tags G d i.1),Tendsto (fun v=> Y v i k t) L (𝓝 (listK i (Aᶠ) k t)))(u:6≤d)(hQ:Maxer L q) (X:ι→TPoint G d)(H:∀ i∈resident h T S W K M d u,Billed L q (fun j=> receives i (Y j) (X j))): Across L q ℝ X:=by
    have hp:=hotel d (Aᶠ) (independence h T S W K M u); let f(i)(j:Sensor G d):= receives j (Y i); refine Foundation.costs _ f hp (fun i x=> ?_) hQ X H; exact Tendsto.add ((p i.1 _ _).const_mul (x.2:ℂ)) (tendsto_finsetSum _ (fun j _=> p i.1 0 (update i.2 j (x.1.val (i.2 j))))) -- type classes
end Query
-- payable tangent using Gram dual all projected.What about null variables.Without positivity suffice diagonal.V.Cong.
local notation "pK"=> Normalize.Sec G d
lemma gram_lock (a:Axis)(U:ι→ Gram.BI (Normalize.Sec G d))(p:∀ x:Tags G d 2,Tendsto (fun j=> U j x) L (𝓝 (scene ( Gram.nodes a ) d x)))(hQ:Maxer L q) (X:ι→ Normalize.Sec G d)(Y:∀ p':Normalize.Sec G d,Billed L q (fun i=> U i ![X i,p'])): Across L q ℂ X:=by
    let v:=scene (Gram.nodes a) d (G:=G); let K(x:pK):= Gram.acts v x; let B:= Module.finBasis ℂ (Normalize.Sec G d)
    have ht (x:pK)(u:∀ i:pK,K i x=0): x=0:=by
        obtain ⟨k,p⟩:= Adapter.gap _ (Gram.prescribed a B); let t:= Gram.flipE a x; have hs:= p.2 (B.equivFun x); rw [← Gram.cone] at hs; change _≤ (K t x).re at hs; rw [u t] at hs; by_contra h'; have v: 0<‖B.equivFun x‖:= norm_pos_iff.mpr fun y=>h' (B.equivFun.injective (y.trans (map_zero _).symm)); have hz:= (mul_pos p.1 (pow_pos v 2)); exact hz.not_ge hs
    exact Foundation.costs K (fun i (t:pK)=> Gram.acts (U i) t) ht (fun i x=> p ![x,i]) hQ X fun i _=> Y i
end YM.SignedWilsonExpansion.Commission.Method
