import YM.RemainderComparison.Fallow.Actions
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Fallow
open Function Filter Lattice RG Wilson MeasureTheory Push Push.AbsoluteSums Marker Finset
open Solos Mosaic Verse Serif Flues WickReps Ethereal Jolt Lacuna Lobby Passion GridRenewal.Rain PhysicalNext.Repeat WardBin.Crest
open Source Labels Next.Foundations Local Work.G08 AnalyticBridge VerifiedReset VerifiedReset.Seat
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {θ ι:Type}{D:ι→ Finset θ}{Q:θ→Type*} [∀ i,NormedAddCommGroup (Q i)][∀ i,NormedSpace ℝ (Q i)]
variable {G:Gauge}{n:Side}{I J' :Type}[Countable I] [Countable J']
variable (T:Manor G n ι (Audited Q) I)(T':Manor G n ι (Audited Q) J')(V:Rep G n)(R:ι→Support n)(Z:Set ι)
variable (i:θ)(F:Plane G n θ)(X: Hol G)(H:Yard ι (Audited Q) G n)(a b :Audited Q)
variable [Fintype θ][DecidableEq θ](J:Census θ)(z:ι→Marker.Poly J)(q:θ→ℝ)
set_option quotPrecheck false
local notation "p"=> V.p
variable (hV: V.activities.forced=H.more)(hv: V.activities.K=Ethereal.dusk H Z b)
variable (h:H.Sounds V.p R)(hh:Jolt.Orbit H Z)
variable {w σ v v' w' s t y :ℝ} {k r: ℕ}
variable (hA:AxisG V.p F X w r v') (hp:Passion.Precepts T V.p R Z D σ t)(hp': Precepts T' V.p R Z D σ y) (hx:Placed R F D) (he:F.exam i)
variable (h₀:Passion.Lodge T V.p R Z F X SeatD.MaskType.exactM D s)(he':Passion.Lodge T' V.p R Z F X SeatD.MaskType.exactM D w')
variable (hr:Passion.Oriented D J Z z)(hq:Serif.Chorus J q Z z k)(hm: H.Pays Z k V.p.B V.p.supportExponent v)
variable {κ x:ℝ}(hw: v ≤ κ*x)(hk: 0 < κ) (hb:0≤x)
local notation "A₁" => cash T p R Z F X SeatD.MaskType.exactM z D a
local notation "A₂" => cash T' p R Z F X SeatD.MaskType.exactM z D a
local notation "f₀" => scoreP Z J i H a z
local notation "o"=>(F.visor i).origin
local notation "S"=>(F.visor i).sectionQ
local notation "F'"=>(F.visor i).basis
-- old payment.Plot. SEM.Pushing LE.B.Anal_Ph...
local notation "Ψ" => (q i)⁻¹
set_option quotPrecheck false
local notation "Θ" U:max => (Complex.ofReal (Real.exp (V.exponent U))) • (cyclone ((∑' i,A₁ U i)+(∑' i,A₂ U i))*(∑' i,H.gala V.p Z z a U i))
local notation "M₀" U:max=> Fallow.music T p R Z J X F a 0 z i U
local notation "M₁" U:max=> Fallow.music T' p R Z J X F a f₀ z i U
-- HEADER self-cost. consumer Θ Weighted.D.Ob. statement pointwise.St.C. with Θ yield
include hV hv h hh hA hp hp' hx he h₀ he' hr hq hm hw hk hb
lemma passes (f:players T R Z F D i↪ℕ) (f' : players T' R Z F D i↪ℕ) :
    let A:= M₀ f
    let B:= M₁ f'
    let C:= Fallow.plus A B
    C.Format o X V∧A.Format o X V∧B.Format o X V ∧ A.remBound o V κ (Ψ*s) ∧ (F').coeffSize A.x≤ Ψ*s∧ B.remBound o V κ (Ψ*(w'+x))∧
       Local.ForceCost p V.activities C.forced (κ*(Ψ*x))∧ (F').coeffSize (C.x-A.x)≤ Ψ*w' ∧ C.remBound o V κ (Ψ*s+Ψ*(w'+x)) ∧
       ∀ U: Config G n,(Θ U|>.part J.quiet)=(↑(V.eval U):ℂ) ∧ (Θ U|>.part (J.fire i))= C.density o S V U:=by
    intro A B C; obtain ⟨hy,hΩ⟩:= Fallow.emptyF V.activities o V.p
    have hn:Ψ* v≤κ*(Ψ*x):= (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr (hq.votes _).le)).trans_eq (mul_left_comm ..)
    obtain ⟨t,hT,hx'⟩:= Fallow.purse R Z J i F H a z V hV h hx hr hq v hm
    have hg:Local.ForceCost V.p V.activities f₀ (κ*(Ψ*x)):= ⟨t,budget_loosen hT hn,hx'⟩
    obtain ⟨hb,hQ,hB⟩:= Fallow.eulogy T V.p R Z J X F a hp hA hx q V 0 h₀ f hq hk rfl hy (show Local.ForceCost V.p V.activities 0 (κ*0) from by rwa [mul_zero]) (le_refl _)
    obtain ⟨hb',hQ',hB'⟩:= Fallow.eulogy T' V.p R Z J X F a hp' hA hx q V f₀ he' f' hq hk rfl (Fallow.earned R Z J i F H a z V hV h hx hr) hg (mul_nonneg (inv_nonneg.mpr (hq.votes _).le) ‹0 ≤ x›)
    have hvC:C.forced=f₀:= zero_add _; rw [add_zero] at hB; rw [←mul_add] at hB'; refine ⟨tied V hQ hQ', hQ,hQ',hB,hb,hB',hvC ▸ hg, ?_,added V hB hB', fun U=>?_⟩
    · rw [show C.x=A.x+B.x from rfl,add_sub_cancel_left]; exact hb'
    have hm₀:= (Passion.title T V.p R Z F X SeatD.MaskType.exactM hp h₀ _ _ _ hA z U a hr hq a).1
    have hm₁:= (Passion.title T' V.p R Z F X SeatD.MaskType.exactM hp' he' _ _ _ hA z U a hr hq a).1
    obtain ⟨hc₀,hx₁⟩:= Fallow.stage T V.p R Z J X F a hr he hp hA hx q V 0 h₀ f hq rfl U hm₀
    obtain ⟨hc₁,hx₂⟩:= Fallow.stage T' V.p R Z J X F a hr he hp' hA hx q V f₀ he' f' hq rfl U hm₁
    refine Fallow.veil V.p Z J i H a b U z hr V hV hv hh rfl C o S hvC _ ?_ ?_ (Flues.yard_paid _ p _ _ _ _ hq hm V.p.exponent_pos.le).2
    · rw [Poly.part_plus,hc₀,hc₁,add_zero]
    rw [Poly.part_plus,hx₁,hx₂]; exact Fallow.jointly V U hB hB'
end YM.RemainderComparison.Fallow
