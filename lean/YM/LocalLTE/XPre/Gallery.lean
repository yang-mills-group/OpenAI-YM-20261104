import YM.LocalLTE.XPre.Far
import YM.LocalLTE.Ticket.Pip
/-!
# Canonical-Consumer -> Lamp stamps at all requests at payroll
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.XPre
open Function Finset Filter Set MeasureTheory Lattice Wilson RG
open Extra.Histories Push Local Motion Extra.Multi
open LocalLTE.Fan LocalLTE.River LocalLTE.Vinca
open PhysicalNext.Repeat Lotus Blush Progress.DirectedRecipe
open YM.MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {ι: Type}{G:Gauge}{c f:Side}{S:StepData c f} {R : Rep G f} {C: Rep G c}
    {κ K ν t u q r s b:ℝ} {A:Activities G f} {d p m l:ℕ} {o:Site f}{o':Site c}
open AbsoluteSums Animals Next.Foundations Source Planned.GuardedAtom
variable {v w:ℂ}{X:Wing→Prop}{M:ι→ Leaf R}{g:ι→ℂ}{φ:MergeProof.Response G c}{L:GaugeDoor R C}
variable {E:Config G f→ℂ} {Z: Res G f}{W : Res G c}
variable (h:Circuit X L d κ p l o o' v E Z W w t u b)
set_option quotPrecheck false
lemma zero_can (ht:0≤t)(hb:0≤b)(hv:0≤u)(x:ℂ): Circuit X L d κ p l o o' v (fun _=>x) 0 0 x t u b := by
    let ψ:MergeProof.Response G c:=0; let e:Empty→Leaf R:= Empty.elim; let z:Empty→ℂ:=fun _=>0
    refine ⟨Empty,inferInstance,e,z,ψ,fun _=>False, ?_,?_ ,fun i=>Empty.elim i⟩
    · refine ⟨fun i=>Empty.elim i,⟨fun i=>Empty.elim i,Summable.of_finite,by simpa using ht⟩,stackFee (Attainment.blank _) hv,fun U=>?_,fun j U=>?_,fun j U=>?_⟩ <;> simp [ψ, MergeProof.hook] -- h simpl.
    exact ⟨fun i=>Empty.elim i,Summable.of_finite,by simpa using hb⟩
-- projection.We expose Atlas credentials in H aperture.
-- history.Pe
local notation "B'"=> localSection G d
local notation "F"=> ((Labels.frames G).level d)
local notation "φB"=> hol G
structure Prices where
    beam:ℝ
    grant:ℝ
    canopy:ℝ
    future: 0 ≤ beam
    pole: 0≤ grant
    crown:0≤canopy
-- `Audited`.
structure Permits (R : Rep G f)(C:Rep G c) (X:Wing→Prop)(L:GaugeDoor R C)(d:ℕ)(Λ:ℂ)(V:Vinca.Gateway ((Labels.frames G).level d) (hol G) R c)(A:Prices)(κ:ℝ)(p l:ℕ):Prop where
    reserves (i: ((Labels.frames G).level d).Index) : i≠0→ Circuit X L d κ p l (0:Site f) 0 Λ ((Extra.Histories.primary (0:Site f) (Size.axis ((Labels.frames G).level d) i)).exponentialEntry 0 (localSection G d) R) 0 (profile C.activities (V.core i).forced) 0 A.beam A.grant 0
    regular (f' g: Config G f→ ℂ) (U:Support f)(a b c:ℝ)(hf:RegFit R 0 d (hol G) U f')(hp: RegFit R 0 d (hol G) U g)(ht:R.p.supBounds 0 U f' a)(he:Canvas (localSection G d) κ l p R.p U g b)(hx:R.p.supBounds 0 U (f'-g) c):
       Circuit X L d κ p l (0:Site f) 0 Λ (masked R.p.threshold U f') 0 (profile C.activities (V.reader f' U a hf ht).forced) 0 (2*(R.p.mass U b+R.p.mass U c)) (A.canopy*R.p.mass U a) (2*R.p.mass U c)
    forced (f':Config G f→ℂ) (j:ℕ)(a b:ℝ)(h:f'≠0)(hv: X (.gasKey j))(ht:SlotFit R 0 j f')(hc:∀ U,‖f' U‖≤a)(hx:∀ U,‖f' U‖≤b) : let v:=R.p.mass (R.activities.forced j).support b; Circuit X L d κ p l (0:Site f) 0 Λ 0 (exactGas R.activities j f') (profile C.activities (V.flag f' j a ht hc).forced) 0 (2*v) (A.canopy*v) (2*v)
variable {C' B:BudgetPoint} {κ q r b:ℝ}
end YM.LocalLTE.XPre
