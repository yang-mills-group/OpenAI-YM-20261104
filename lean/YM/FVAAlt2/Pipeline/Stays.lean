import YM.FVAAlt2.Pipeline.Memory
/-! # Cast-free exact projection of linear drivers between the actual Reel.G and the period Kernel.Matrix.Sp.Calc. Needed to take `p→∞`. Stalk convergence is not asserted by this transfer identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Pipeline
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m :ℕ} {G:Gauge} {R X:Type} [DecidableEq R] {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side}
open Oracle Period.Field
variable (C:Circuit M N) (Y:Oracle.Program Q)(Φ:∀ P:Patch,P.Branches Q G) (Γ: History G)(K: Bulk.Chain Γ)(P: Period.Field.SeriesT C Q Γ)
variable (S: Marker.Census R)(u:R) (A: X→ Boot.Scout (G:=G) m)
variable (L:Page M→ Binding.Scale)
variable (p:ℕ) -- period
namespace See
variable {C Γ}
local notation:max "x_" k:max=> P.vol k
set_option quotPrecheck false
local notation:max "f_" k:max => (Γ.S.side (P.vol k) p)
local notation:max "U_" k:max => P.stepData C Γ p k
local notation:max "F_" k:max => Halo.bios ( P.stepData C Γ p k )
local notation:max "P_" k:max => P.records C Γ p k
local notation:max "J_" k:max => directive (P.stepData C Γ p k)
local notation:max "K_" k:max => ( P.readyKin C Γ K p k )
local notation:max "w_" k:max=> Page.opening M k
local notation:max "B_" k:max=> ( Boot.ink S u Γ (P.vol (w_ k)) p (A k) )
-- Reader constructor
local notation:max "M_" x:max => ( Circuit.mural G L x )
local notation:max "Z_" x:max => C.bore G Φ L x
open FreeResolvent ( flatten )
open Oracle.FVAAlt2.Primary Matrix
section Reader
variable {I J I' J':Type}
def Ascent (W:I→J)(X':I'→J')(U:Layer I I')(V:Layer J J') : Prop:=∀ i j,V (W i) j= Stalk.collect X' (U i) j
def Confirm (W:I→J)(X':I'→J')(U:Layer I I')(V:Layer J J') := Ascent W X' U V ∧ Ascent X' W (Function.swap U) (Function.swap V)
lemma Ascent.ofLedger {T T': Side→Type}(H:Quarry I J T)(H':Quarry I' J' T'){s:Side}{K:Layer I I'}(hp:Albedo H H' K): Confirm (H.swrap s) (H'.swrap s) K (ledgerRow H H' K s):=by
    refine ⟨fun i j=> ledger_at H H' K hp i s j,fun i j=>?_ ⟩
    rw [← ledger_at H' H _ hp.swap i s j]; exact congr_arg (fun k:Matrix (T' s) (T s) ℝ=> k (H'.swrap s i) j) (Oracle.Ledger.rev H H' s hp).symm -- defeq swap
end Reader
local notation:max "d_" i:max => ( Arm.Pred (U_ i) ( F_ i ) ( K_ i ) )
local notation:max "e_" i:max => ( Arm.night (U_ i) (F_ i) (K_ i) )
set_option quotPrecheck false
-- holy primary ports
variable {I:Type}
theorem projection {G:Gauge}{c f:Side} (K: KernelChoices) (P: Patch)(Z:∀ P':Patch,P'.Branches K G)
  (w:StepData c f) (A B:Bed)(H:Bloch.Cross P.L (Exterior.TypeFace 1) (Exterior.TypeFace 1)) {O:ChartRatio G}{q:RG.Clip}{U:PathData G}
  {τ σ η α:ℝ} {δ: RG.Clip} (T:Comparison.RG02.Bulk.Kernel w q U O)(hx:w.patch=P)(hp:w.kernel=K)(he : YM.FVAAlt2.Period.Rent.Right q U f A)
  (hn: Hall A τ σ η δ)(h:Oracle.BidP P K A B H τ α): let F:= Halo.bios w; let I:= imprint G f; let V:= imprint G c
               Confirm I V ( projectionQ P K H G ) ( Arm.Pred w F T )∧ Confirm I I ( hearth P K G A hn (Z _)) ( Arm.night w F T ) :=by
    rcases w with ⟨w,k,h⟩; change w=P at hx; change k=K at hp; subst w; subst k; have hw:f=c*P.L:=Subtype.ext h; subst f; let W:= avenue P K c; intro F I V
    have he': Arm.Pred W (stemF P c) T=ledgerRow (blockQ G P.L) (linksQ G) ( projectionQ P K H G ) c:=by
       apply Oracle.matrixQ; intro x; rcases (Arm.inventory c G).surjective x with ⟨u,rfl⟩; rw [Pred, LinearMap.toMatrix'_mulVec, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Arm.high_g ]; change _=_*ᵥ flatten u; exact (Oracle.FVAAlt2.Primary.mean K P H A B hn ‹Oracle.BidP P K A B H τ α› c T he u).symm
    have hx:I=( blockQ G P.L).swrap c:= funext fun i=> (Oracle.v_same ..).symm
    constructor
    · change Confirm _ _ _ (Arm.Pred W (stemF P c) T); rw [hx,he']; exact Ascent.ofLedger _ _ (placates P K H G)
    rw [hx,show Arm.night _ F T= ledgerRow (blockQ G P.L) (blockQ G P.L) (hearth P K G A hn (Z P)) c from (Oracle.FVAAlt2.Primary.panel K P A hn (Z _) c T he (directive W)).symm]; exact Ascent.ofLedger _ _ ( phaseT P K G A hn (Z _) )
theorem stay (x:Flap M):
        let E:= imprint G (Γ.S.side (P.vol x.next+1) p); let D:= imprint G (Γ.S.side (P.vol x.next) p)
        Confirm E D ( C.sails Y G x ) ( d_ x ) ∧ Confirm E E ( C.pulses Y G Φ x ) ( e_ x ) :=
    by exact projection Q (C.pactP x) Φ (U_ x) (C.tables Y x.prev) (C.tables Y x.next) (C.tells Y x) (K_ x) (P.pact x p) ( P.creed x p ) ( P.upstream Y C Γ K p x ) ( C.honored Y x.prev |>.card ) (C.predicted Y x)
end See
end YM.RegulatorIR.FVAAlt2.Pipeline
