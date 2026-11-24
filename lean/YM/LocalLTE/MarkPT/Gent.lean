import YM.LocalLTE.MarkPT.Hat
import YM.LocalLTE.MarkPT.Motes
/-! Orbit-shared explicit mark proposal. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
-- parity.Y allele tall cone factor.Deferred.B.Gouge.
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')
variable (Φ:ℕ→ℝ→ Config G f→ℝ)(Ψ:ι→ℝ→ Config G f→ℝ)
open Weft
open East FrameBox
-- once planning.L. $radius.A.Messages. Photo rebate. anchored per-slot. No adapters lean type.This supply supports ANY derived petals. Calendar explicit strong.Q.P
open AnalyticBridge VerifiedReset Collection Price
variable {κ K v:ℝ}
variable (l:ℕ)(X:(i:Stars H M)→Grove (origin M H i))(hp:2*(2*(East.stagnate q Q.halo*radiusB t))≤ c.val) (hX: East.stagnate q Q.halo*radiusB t < l*radiusB t)
variable (ε:ℝ)(w:ι→ℝ)(p:BudgetPoint) (s:ℝ) (d m Pk:ℕ)
-- Full native denominators. supplies
local notation "U'"=> East.stagnate q Q.halo*radiusB t
local notation "Z'"=> sitesP M H q n r₀ A' l
local notation "Y'"=> betaF G t L
-- while using forecasts, can charge ``blank`` K coefficients, *NOT THE ACTUAL K*.
open Merge.Photo Merge.Motion Marker Overlay Next.Foundations Progress.DirectedRecipe
variable {E:Type}[DecidableEq E] (Qt: Marker.Census E) [Fintype ι] (kp:ι→Poly Qt)(wp:E→ℝ) (hw:∀ i,0<wp i)
    (hc:∀ i,Poly.price wp (kp i)≤1) (b:E→Site c) (i:E) (P:Rep G c)
local notation "X0"=> sitesP M H q n r₀ A' l
local notation "QX"=> ghost M H q n r₀ A' w l P Qt kp b i
local notation "T" q=> (QX q)
variable (f': Stars H M→ Config G c →ℝ)
variable {U V ν:ℝ}
local notation "ℓ"=> (Fan.offerC M H X0 Qt b)
local notation "r"=> (Fan.tapsC Qt)
lemma idleG (hp:∀ i,P.p.Regular (sitesP M H q n r₀ A' l i) (f' i)): (T f').Active:= by
    let k:= fun (_:ℝ)(_:Finset ι)=> (0:Ovens.Code G c); have h:= Fan.shelf M H w f' X0 Qt kp b i P k
    let v0:= T f'; let v(s:Metering M H X0 Qt b):= ℓ s; let u(x:libraries Qt):= r x
    have ht (j:ℕ)(h:j∉Set.range ℓ): v0.support j={b i}∧ v0.rays j=Qt.fire i∧ v0.H j=0:=by dsimp only [v0,ghost,opalescence]; exact ⟨Function.extend_apply' _ _ _ h,Function.extend_apply' _ _ _ h, blank _ _ h⟩
    change v0.Active; refine ⟨fun z=>?_, fun x j hj=>?_, fun x=>?_, fun x j=>?_,fun x j h k'=> False.elim (h rfl), fun _ _ _ _ _ _=> rfl,fun x j _ h=>False.elim (h rfl), fun _ _=> measurable_const, fun _ _ _ _=> rfl⟩
    · by_cases he:z∈Set.range ℓ; · obtain ⟨z,rfl⟩:=he; rw [show v0.rays _ = _ from h z|>.2.1]; exact z.property.1
      rw [(ht z he).2.1]; exact Finset.singleton_nonempty _
    · by_cases he:x∈Set.range ℓ
      · obtain ⟨z,rfl⟩:=he; rw [show v0.rays _= _ from h z|>.2.1] at hj; rw [show v0.support _=_ from h z |>.1]; exact z.property.2 (mem_image_of_mem _ hj)
      rw [(ht _ he).2.1] at hj; rw [(ht _ he).1,show j=i from Finset.mem_singleton.mp hj]; exact Finset.mem_singleton_self _
    · by_cases he:x∈Set.range ℓ
      · obtain ⟨z,rfl⟩:=he; rw [show v0.support _=_ from h z|>.1,show v0.H _=_ from h z|>.2.2]; exact regular_smul _ (Blush.ornate (hp z.val.1))
      rw [(ht _ he).2.2]; exact unspent _ _
    by_cases he:j∈ Set.range r
    · obtain ⟨j,rfl⟩:=he; rw [show v0.marks x _=_ from Fan.falls M H w f' X0 Qt kp b i P k j x|>.1]; exact j.property
    rw [show v0.marks x j=Qt.fire i from (by dsimp only [v0,ghost,opalescence]; exact Function.extend_apply' _ _ _ he)]; exact Finset.singleton_nonempty _
include hw hc
lemma coldQ (hw':∀ i,0≤ w i)(hP:P.p.supportExponent≤ U)(he:GrowsP M H P.p X0 w U V f' X0)(hx:0<ν): (T f').Active∧ (T f').Radial wp 0 V 0 ν:= by
    obtain ⟨V',hp,hv,hΨ⟩:=he.lights
    refine ⟨idleG M H q n r₀ A' l w Qt kp b i P f' (fun x=> (hv x).1), hw,fun j=>?_,hx, Fan.superscrip M H w hw' f' X0 Qt kp wp hw hc b i P (fun _ _=>0) he hP,0,fun x y=> ⟨le_rfl,fun z=>?_⟩,fun i=>?_⟩ -- nested.B prop
    · change wp j * ‖(0:ℂ)‖ ≤0; rw [norm_zero,mul_zero]
    · change ‖(0:ℂ)‖ ≤0; rw [norm_zero]
    simp_rw [Pi.zero_apply, BudgetPoint.mass,mul_zero,ite_self, zero_mul]; exact ⟨fun _=> le_rfl,summable_zero, (by simp)⟩
-- The roster H is a linear ledger in all leaf sectors without invoking truth.(If headers depend on layout use Infra.)
omit hw hc
def viewG : (Stars H M→ Config G c→ℝ) →ₗ[ℝ] (ℕ → Config G c→ℂ) where
    toFun f:= (T f).H
    map_add' f g:= sub_eq_iff_eq_add.mp (by
        have he: ((T f)|>.H)= ((T (f+g))|>.H)-((T g)|>.H):= by
             have h : f=f+g-g:=eq_sub_of_add_eq rfl
             exact (congr_arg (fun x=> (T x)|>.H) h).trans (Fan.dividesV M H w X0 Qt kp b i P (fun _ _=>0) (f₁:=f+g) (f₂:=g))
        exact he.symm)
    map_smul' a f:= by
        funext j x; let k:=fun (_:ℝ)(_:Finset ι)=> (0: Ovens.Code G c)
        change ((T (a • f))|>.H j x)= (↑a:ℂ)* ((T f)|>.H j x)
        by_cases hu:j∈ Set.range ℓ
        · obtain ⟨j,rfl⟩:=hu; rw [show ((T (a • f))|>.H (ℓ j))= _ from Fan.shelf M H w _ X0 Qt kp b i P k j|>.2.2, show ((T f)|>.H _) =_ from Fan.shelf M H w f X0 Qt kp b i P k j|>.2.2]; unfold chimes; simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
        have hv (f): ((T f)|>.H j)=(0:Config G c→ℂ):=by dsimp only [ghost, opalescence]; exact blank _ _ hu
        rw [hv,hv]; exact (mul_zero _).symm
end YM.LocalLTE.Fan
