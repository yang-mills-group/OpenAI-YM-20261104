import YM.RGComparison.Core16.Silk.Soil
/-!
# Transport native local-germ price kernels from P STEP input by period replay frames

Shim (chosen tree arbitrary at smallest period). Works on rate shape Halo through fixed
Θ contour, apertures inherited. Doesn't change step S. This lemma is BEFORE re-expression
`grad H` costs (Stencil model leases paid already by post-L templates). Need still price
source lifts reading
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Precision Finset
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame Parcel Parcel.Oven
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{A D I J T k:Type}[Fintype I][Fintype J]
   {C c F f: Side} {P:Patch} (K:KernelChoices) {W:Oven P} {e : f.val=c.val*P.L.val} {E:F.val=C.val*P.L.val} {d : ℕ}
   (hC:C.val=c.val*d)(hc:2 ≤ c.val)

-- DON'T use local notation referencing section Vars INSIDE header of section variable (important for avoiding Lean :unreachable linter during dev).
local notation "LX"=> Lace.project (h:=e) (H:=E) hC hc
local notation "S"=> StepData.mk P K E
local notation "S0"=> StepData.mk P K e
set_option quotPrecheck false
local notation "∂L"=> zoom E e hC
local notation "∂B"=> (show c.val∣ C.val from ⟨d,hC⟩)

variable {B' : Forest (StepData.mk P K E).ratio} {B: Forest (StepData.mk P K e).ratio} (hF:Pinnage (zoom E e hC) B' B)
include hc hC
lemma fitted (i:Forest (S0).ratio): ∃ j : Forest (S).ratio,Pinnage (zoom E e hC) j i:=by
    let l:=LX; let a: Forest l.r:=i; let b:=l.repeater a; have h:l.Fitted a b:= ⟨fun x=> rfl⟩; exact ⟨b,fun z j=> h.pines (z,j)⟩

local notation "padB"=> Hut.pad («S»:=S) B'
omit hc hC in
lemma beacon_lease {I k T A D:Type} {X:Shelf G A D}(P:Planet X F I k T)(n:ℕ)(u:Site F): Lease P (fun i=> n-separation u (P.loc i)):= by
    refine ⟨fun i j=>?_⟩; have h:= separation_triangle u (P.loc i) (P.loc j); omega
include hF
omit hc in
lemma pinned_inj {v}(hv:2*v<f.val)(u:Site F): Set.InjOn (projectStem ∂L hF) {i|0 < v-separation u (padB i)}:= by
    intro i hi j hj he; change 0< v-separation u (padB i) at hi; change 0< v-separation u (padB j) at hj; exact within_one (role_nest K hC hF) u hv (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hi)) (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hj)) he

lemma stencils {X:Shelf G (PlaqAxes⊕Axis) W.Xways} (Y:W.Offers X K) (H: Bid.Larger («S»:=S) (G:=G)) (H': Bid.Larger («S»:=S0) (G:=G)) (hv:2*X.sector.b<f.val)
    (u:Directions G c)(hu:∀ i,‖u i‖ ≤ X.Q) {v:ℕ} (b:ℕ)(p:ℕ)(z:ℝ)(he:Reel X z p b)(l : Rail G B'.Free)(hl: List.length l ≤ b)
    {x:Site F} (hK:∀ i∈l,separation x (padB i.1)+v ≤ f.val/3) (j) (hj:j≤p) :
    let Ω:= parcela K (d:=E) X B' (vectorCover ∂B u); let Y0:=parcela K (d:=e) X B u
    |nth j (price Ω l)-nth j (unfoldR (price Y0) (projectStem ∂L hF) l)|≤ z / costLamp X v := by
    intro U V; let n:= f.val/3; let Z t:= n -separation x (U.loc t); refine he _ _ _ _ _ _ _ _ _ _ _ _ _ _ U V (paints _ Y ?_ H) (paints B Y hu H') _ _ (ministry K hC hc hF hv u) Z (beacon_lease U n x) (pinned_inj K hC hF (by omega) x) l hl v ?_ j hj
    · exact fun i=> hu _ -- success?
    intro i hi; have h:=hK i hi; change v≤ f.val/3-separation x (padB i.1); omega
end YM.RGComparison.Core16.Silk
