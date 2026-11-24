import YM.FVAAlt2.Pipeline.Keeps
/-! # Public countable scope. Clock epochs & each actual field instruction all at fixed period, not the Theorem OIR transport projection result. Unearned Uniform comparison still requires convergence Lane. This theorem is for the Period.P.Frame.*, not carrying prices to ξ.ShapeFlags. -/
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

-- degree equality & exceptive. propagate both ways!
local notation:max "Z_" x:max => C.bore G Φ L x
local notation "Z"=> work Φ K P L p
local notation "W"=> observe Φ K P A L p
variable (r:ℕ)(T:Times (L:=L) r)[Fintype R]
local notation:max "t_" k:max => T.cloth k
local notation:max "Z₀" k:max=> Recv P p k ( Z (Flap.prev k ))
local notation:max "W₀" k:max=> Recv P p k ( W (Flap.prev k ))
local notation "R!"=> Prepared Φ K P S u A L p r T
variable (hL:∀ x:X,L (Page.opening M x)= Clocks.flat)
-- cast across relation. height cutoff.Stable
local notation:max "U'" k:max => Colors S G (Γ.S.side (P.vol k) p)
include hL Y Φ
lemma hire : ∃ G₀:Agenda P S p, Setup K P S u A L p r T G₀:=by
    let F (k):= { y:(U' k) // R! k y }
    have funR (f:Flap M) (v:F f.prev): Nonempty ( F f.next ) := by obtain ⟨z,H⟩:= See.next Y Φ K P S u A L p r T f v.1 v.2; exact ⟨⟨_,H⟩⟩
    let ψ : ∀ i:Page M,F i:= Halo.seriesC (fun x=>( ⟨ ( B_ x ), See.starts Φ K P S u A L p r T hL x⟩: F ( Page.opening M x ) )) (fun i y=> Classical.choice (funR i y))
    refine ⟨fun i=>(ψ i).val, {top := fun _=>rfl, allows:= fun i=> ⟨ (ψ i).property.1.certified,(ψ i).property.2.2 ⟩, walks := fun i=>?_ } ⟩
    exact (( checked Y Φ K P S u A L p r T i (ψ i.prev).val (ψ i.next).val (ψ i.prev).property ).mp (ψ i.next).property ).1
-- Wait: Walk Checked requires Prev relation. Existence choosing ANY Post prep independent of prev (yes).
lemma handles {U: Agenda P S p} (h: Setup K P S u A L p r T U): ∀ i, R! i (U i):=by
    refine Page.proves ?_ ?_
    · intro x; rw [h.top]; exact See.starts Φ K P S u A L p r T hL x
    exact fun i hi=> ( checked Y Φ K P S u A L p r T i (U i.prev) (U i.next) hi ).mpr ⟨ h.walks i,h.allows i.next ⟩
-- Output formula for operative.Task.Q (same price HAS orientation read through all Script). local model branches θ unchanged.
lemma observes {U:Agenda P S p}(h: Setup K P S u A L p r T U)(b:Page M)(x:fieldDir G (Γ.S.side (P.vol b) p) 1) {i:ℕ}(he:i≤r): prime P S u L p r T U (x:=b) x i= Uniforms.cuff (W b) m i x ∧ visible S ((P_ b).clip) ((P_ b).path) (t_ b) (U b) i x=Uniforms.cloth ((P_ b).clip) ((P_ b).path) ( Z b ) i x:=by
    obtain ⟨H,hq,hK⟩:= handles Y Φ K P S u A L p r T hL h b; exact ⟨ hq.earned i he x,isReal S r _ _ _ _ _ H x i he ⟩
lemma scalar_here {U:Agenda P S p}(h: Setup K P S u A L p r T U)(b:Page M){i:ℕ}(he:i≤r) : (prime P S u L p r T U (x:=b) 0 i)=↑((observe Φ K P A L p) b i 0 Fin.elim0):=by rw [(observes Y Φ K P S u A L p r T hL h b _ he).1]; unfold Uniforms.cuff; rw [flavor_lo,show FreeResolvent.flatten (0:fieldDir G (f_ b) 1)=0 from rfl,← Prim.speaking, Prim.starts]
lemma consistent (s:ℕ)(W':Times L s){U U₁:Agenda P S p}(h: Setup K P S u A L p r T U)(q: Setup K P S u A L p s W' U₁)(t:Page M)(x:fieldDir G (f_ t) 1){e:ℕ}(he:e≤r)(hs:e ≤ s): prime P S u L p r T U (x:=t) x e= prime P S u L p s W' U₁ (x:=t) x e:= (observes Y Φ K P S u A L p r T hL h t x he|>.1).trans ((observes Y Φ K P S u A L p s W' hL q t x hs).1.symm)

omit hL Y Φ
include hL
lemma prices : ∃ T: Times L r,True:=by
    let c(z:Page M):= if z.downW=0 then Boot.dormant else Ribbon.budgetV (L z) r; refine ⟨{ cloth:= c,top:=fun x=>if_pos rfl,holds:= ?_ },trivial⟩; intro w; unfold c; split
    next hh=> rw [show w=Page.opening M w.bindW from ?_,hL]; exact Boot.dormant_l r
              rcases w with ⟨w,j,H⟩; change j=0 at hh; subst j; rfl
    next _=> exact Ribbon.lives _ _
end See
-- Usage.Y_ACT Next.Epoch.FVA. bind T+Φ etc simultaneously to Run & Clock and gather chronics.F.Set.UseBoot Labels.lean later.
end YM.RegulatorIR.FVAAlt2.Pipeline
