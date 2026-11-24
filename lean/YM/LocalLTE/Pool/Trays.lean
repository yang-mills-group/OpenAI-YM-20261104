import YM.LocalLTE.Pool.Table
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
local notation "W" => (bank n G M)
local notation "P" => iceCap (n:=n) G M p c x κ
variable (hs : Reliable G κ k) (hG:G.Simple)(hn:20<n.val) (hb:Decent c p)
lemma rota_bill (h:Reliable G κ k)(j M:ℕ) (i:Key n)(hG:G.Simple)(hn : 20<n.val): Comic G (ew i.native) p (rota G i j M κ):=by
    unfold rota; split
    next h'=>
       have he:= VerifiedReset.reg_larger (accrual_regular (b:=p) (G:=G) i) ((shore'₀ i).trans (shore_l _))
       have ht: Comic G (ew i.native) p i.accrual:=by
          have hh:= Start.accrual_null i 1 (G:=G); rw [one_smul] at hh; exact ⟨he,hh.1,fun k i j _ _=> hh.2 ..⟩
       exact ht.pair (plot p h hG hn _ _) -- edit
    split
    · exact plot p h hG hn _ i
    exact Comic.pair (plot p h hG hn _ _) (plot p h hG hn _ _) -- signature includes G?
include hG hs hn hb
open Payments
lemma fitsH : Fittings P W p:=by
    have he : ((W).pours P).RegularFamily p:=by
       let Q:= iceCap (n:=n) G M p c x κ; have h(i: ℕ): Comic G ((W).reg i) p (Q.regular i):=by
          unfold Q; rw [reggo]; split
          next h=>
              let k:=name (Card M n) i
              have he:= rota_bill G p hs k.1 M k.2 hG hn
              exact Comic.scales _ he
          exact Price.flick p
       exact ⟨fun i=>(h i).1,fun i=>(h i).2.1,fun i=>(h i).2.2⟩
    have h(i:ℕ):Trio.Tidy p ((W).softer i) ((P).logarithm i) ∧ ∀ U, (P).logarithm i U ≠0 → ¬ Healthy p.threshold ((W).softer i) U:=by
       let A:= name (Key n) i; let a:= weight c x; dsimp only [Frost.iceCap]; split
       next hx=>
          have he:= usesU G p A; refine ⟨⟨fun U V he' h=> congr_arg (a*·) (he.1.uses U V he' h),he.1.borel.const_smul _, fun k U=> congr_arg (a*·) (he.1.invariant k U)⟩,fun U hu hy=> he.2 U (fun hv=> hu (by change a * Frost.maskH G p A U=0; rw [hv,mul_zero])) hy⟩
       exact ⟨⟨fun _ _ _ _=>rfl,measurable_const,fun _ _=>rfl⟩,fun _ h=>False.elim (h rfl)⟩
    have ht: ((W).pours P).ForcedFamily p:= by obtain ⟨a,b,d₀,u,f,h,X⟩:= Start.forcedFamily (G:=G) (n:=n) hb x; exact ⟨a,b,d₀,u,f,h,X⟩
    refine ⟨he, ht, Frost.rainW G M p c,fun i=> (h i).2,fun i=>(h i|>.1).invariant,fun i=>(h i|>.1).uses,fun i=>(h i|>.1).borel,fun s o=> ⟨Padded.sends (Key.perm s o),fun i=>?_,fun U i=>?_⟩⟩ -- forced not definitional structurally.Could cases.
    · dsimp only [bank]; rw [name_sends,e_h s o]
    dsimp only [iceCap]; rw [name_sends]; simp only [fixed_sends]; split; next h=> rw [Frost.mount G p s o]; rfl
    rfl
end YM.WilsonStartup.Frost
