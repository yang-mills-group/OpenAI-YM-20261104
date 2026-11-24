import YM.GradedFar.Elected.Voters
import YM.GradedFar.Physical.Elevation
import YM.GradedFar.CoreBudget
import YM.GradedFar.Measured
/-!
# Second line of (M.2)

Here it uses the *actual reading* of the book, and calibrates it from the indicated
C5 pins of PoseFit at the moment hierarchy. See `Price` for the test-wise witnesses
on those pins. Exhaustion of the k-proxy cost still pays line (M.2).
-/
namespace YM.FVA2.GradedFar.Elected
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open OPE Orbits GradedFar.Physical Climb Next.UVStress Trace.Pilot
open Integration Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h k j t p : ℕ} (N : YM.FVA2.Register.WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable {R : PhysicalNext.Repeat.Legato.Run G} {f : Extraction.Order} {P : Table R.family.book}
    (U : Spec.Final R.family f P) (J:ℝ → PhysMS.tower P) (lead : PhysMS.Leading U J)

/-- Use in §NearFarDelta's hypotheses: PoseFit supplies for a finite stock
of calls **on this book**, earlier in that proof: in particular (C5), line 1333,
display (motivating this antecedent). Here ask JUST that compact-geometry C5 at
our chosen book's PoseFit calibration (so *not* assuming (F.2),
(F.3) or (G.9)). For example use M-1=k≥2, q=Q_* and those `D_cash-I : Change`.
We explicitly require the specified `t'_ℓ∼g` of that PoseFit hypothesis, at this payout.
`RawCalibration` has just those comparisons *before* undoing field estimates;
no Frame/G.1 physical budget here. One shared k & q & t' & actual Sec-field
adjustment `stand(D r)`, not row-dependent. No C1 assumption. From
`RawCalibration` verify F.3 and the coupling budget in Lean.
-/
def Earlier : Prop := ∃ (k q:ℕ) (t':ℝ→ℝ) (D:ℝ→ Normalize.Change G 6),
    2≤k ∧ 1≤q ∧ k≤q+1 ∧ Tendsto (fun r=> t' r/gYM G r) τ (𝓝 1) ∧
    Tendsto (fun i=>guide G 6 (D i)) τ (𝓝 0) ∧ RawCalibration N (familyPoint U (Wframe N U J) 6) t' k q D

/-- Alternative way to give the preceding PoseFit C5 *only*. Put explicit order `q=Q_*`,
    height `h` covering the used horizon, `k=M-1`. Need only the finitely many determining requests of
    these types (points on full compact calibration, as in 1337). `Answered` on **any
    covering horizon**, wears same W, in S continuum. Positive arities only. -/
def C5 : Prop := ∃ (k q:ℕ) (t':ℝ→ℝ) (h:ℕ) (D:ℝ→Normalize.Change G 6),
   2≤k ∧ 1≤q ∧ k≤q+1 ∧ Tendsto (fun i=>t' i/gYM G i) τ (𝓝 1) ∧
   Tendsto (fun i=>guide G 6 (D i)) τ (𝓝 0) ∧
   ∃ (hd : 6≤h),
     (∀ i:Fin (N.store.survey 6).n, let w := (N.store.survey 6).scope i;
       Elevation.Answered N U (Wframe N U J) w.p (tsupport w.t) q k hd t' D) ∧
     ∀ s:XSpace.Rose.Badge,
       Elevation.Answered N U (Wframe N U J) (XSpace.Rose.missing (XSpace.Rose.tag G) s)
         (tsupport (XSpace.Rose.test N.criterion)) q k hd t' D
include H in
lemma sturdy (h : C5 N U J): Earlier N U J := by
    obtain ⟨k,q,t,h,D,hk,hq,h',hv,hs,hd,H0,P⟩:=h
    exact ⟨k,q,t,D,hk,hq,h',hv,hs,fun i=> Elevation.answers N M H U (Wframe N U J) _ _ q k hd t D (H0 i),
      fun i=> Elevation.answers N M H U (Wframe N U J) _ _ q k hd t D (P i)⟩
variable (hP : Earlier N U J)
include H lead hP
local notation "θ"=>reading U J N
local notation "F"=>familyPoint U (Wframe N U J) 6
-- measured-coupling budget
lemma clocks : Tendsto (fun i=> θ i/g i) τ (𝓝 1) ∧
     ∀ᶠ r in τ, 0 < g r ∧ 0 < θ r ∧ |θ r| ≤ 1 ∧ |θ r| ≤ 2*g r := by
    obtain ⟨k,q,v,D,hk,hq,h',hf,hV,he⟩:=hP
    rw [reading_equal]; have hx:=holds N U J lead 6
    have h0:∀ᶠ r in τ,0<r:= self_mem_nhdsWithin
    exact paid_kinetic N M F v hf H _ D (fun n x=> h0.mono (fun i h=> hx.cont _ h n x))
       (fun n x y=> h0.mono fun i h=> hx.full _ h n x y) hx.fixed hV q k hq h' he hk

/-- The second inequality of (M.2) under the stated calibration hypotheses.
`Main.Match` supplies the formal identification. The physical calibration
uses `Leading` and `PoseFit`. The C5 clock proxy and its bound come from
`NearFarDelta` under the physical hypotheses.
Use `k+1=M`, `q=Q_*`, and take `Dcash-I` in `Change` as in that calibration.

In particular valid for every B in the (M.1) moving range (strong bound for
all T ≥ the stated sufficiently large real T₀). Arity n of Near there
(nonempty for OPE, but price works without that restriction), empty Far ok
(including bounds on that *empty exterior*, not truncating in arity). x and y are
on the separated compacta of relative argument shapes. Formal `Dx ... c`
is a *series*, its singleton-center input in this application being c, in Sec G h,
not a polynomial coupled series in that slot. It takes exactly that `cActual`
(the cropped genuine OPE Coef through Sector h), crop `Dx` after K's inserted on
all Far args as required. Clock is prescribed t(r) reading full Rose call with all
proper subcalls -- measure on continuum, no reliance on picking a spectral phase --
and the same t in every row. Use `coeff_applyFar, Yx_mask, charged_identity, F1,
...`, documentation.
-/
theorem M2_second {X:Set (Points n)}{Y:Set (Points m)} (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m)
     (d:Fin n→ℕ)(e:Fin m→ℕ)(p h:ℕ)(L L':ℝ):
     (∀ᶠ r in τ, 0 < g r ∧ 0 < θ r ∧ |θ r| ≤ 1 ∧ |θ r| ≤ 2*g r) ∧
     ∃ D:ℝ,0<D ∧ ∃ a:ℕ, ∃ T₀:ℝ, 2≤T₀ ∧ ∀ᶠ r in τ, ∀ T:ℝ,T≥T₀→
         ∀ x∈ X, ∀y∈Y, ∀u:Inputs G d, Within L u →∀ v:Inputs G e, Within L' v →
           ‖crop p (θ r) (Yx N M x y u v (Real.log T)) -
              crop p (θ r) (Dx N M y v (Real.log T) (cActual N x u h p (θ r)))‖ ≤
                 D*(T⁻¹^(h+1)+g r^(p+1))*(1+Real.log T)^a :=
     let H' := clocks N M H U J lead hP
     ⟨H'.2, paid H hX hx hY hy d e L L' p h θ H'.1⟩
open MeasureTheory
/-- At the very same order & clock, pairs with any of the *joint* tests (on the
product space x,y) at the same price including ‖B‖ and variation. No dilation of tests. -/
theorem M2_integrated {X:Set (Points n)}{Y:Set (Points m)} (hX:IsCompact X)(hx:X⊆conf n)(hY:IsCompact Y)(hy:Y⊆Outside m)
     (d:Fin n→ℕ)(e:Fin m→ℕ)(p h:ℕ)(L L':ℝ) :
     ∃ D:ℝ,0<D ∧ ∃ a:ℕ, ∃ T₀:ℝ, 2≤T₀ ∧ ∀ᶠ r in τ, ∀ T:ℝ,T≥T₀→
         ∀u:Inputs G d, Within L u →∀ v:Inputs G e, Within L' v →
         let P := fun i : ↥X × ↥Y => crop p (θ r) (Yx N M i.1.val i.2.val u v (log T))
         let Q := fun i : ↥X × ↥Y => crop p (θ r) (Dx N M i.2.val v (log T) (cActual N i.1.val u h p (θ r)))
         ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E],
         ∀ (φ : VectorMeasure (↥X × ↥Y) E) [IsFiniteMeasure φ.variation] (B : ℂ →L[ℝ] E →L[ℝ] ℂ),
           φ.Integrable P ∧ φ.Integrable Q ∧
             ‖(∫ᵛ x, P x ∂[B; φ]) - (∫ᵛ x, Q x ∂[B; φ])‖ ≤
               D * (T⁻¹^(h+1) + g r^(p+1)) * (1+log T)^a * ‖B‖ * φ.variation.real univ := by
     obtain ⟨C,hC,a,T0,p',H'⟩:=GradedFar.tested d e H hX hx hY hy L L' p h
     exact ⟨C,hC,a,T0,p',(clocks N M H U J lead hP).2.mono fun r hr T hT u hu v hv=> H' T hT u hu v hv _ _ hr.2.2.1 hr.2.2.2⟩

end
end YM.FVA2.GradedFar.Elected

