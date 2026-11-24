import YM.Integration.WilsonRootedKioskPhysicalPostWhole
import YM.QuadraticLocal.Shelter.Shadows

/-! Install a born unmasked field on the actual second tap, carrying the
entire first physical Wilson push and its complete original hard inventory. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedFreshMerger
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

open Filter IterationFour PhysicalNext.Repeat.Legato Pert.Asymptotics OPE.Therm


variable {G : Gauge} (X : Run G) 
  {I V : Type} [Countable I] [DecidableEq V] [Fintype V]
  {N per i : ℕ} {L : Side} {T : Type}
  {x e f r s κ w b₀ b₁ z Y Γ K : ℝ} {A₀ : Teller G} {Q : ConnectedActivityE6.Target G A₀}
  {horizon : ConnectedActivityE6.Target.Order G w}
  {tube : Pressure.Tube G (X.family.path.levels.clock.op i per)}
  {P : Rep G (X.family.side (i+1) per)} {P' : Rep G (X.family.side i per)}
  (cash : Cash w x κ L Q horizon z tube P) {k : ℕ} (eyes : Eyes cash P' e Γ Y K k)
  (W : Travel.Walk cash P' e f r s)
  {R : Census V} {o : V → Site (X.family.side (i+1) per)}
  (A : Gallery T I o P R) (weights : V → ℝ) (grant : Seal A weights b₀ b₁)
  (pos : ∀ v,0<weights v) (slots : HasSlots P.p P.activities)
  (cap : ∀ m : R.Mode,m.val.card ≤ k) (bill : 2*(b₀+b₁) ≤ K) (pin : T)


open WilsonRootedKioskOccupiedSlip WilsonRootedKioskSlipCharge
open QuadraticLocal.Shelter

variable {J E I₀:Type}[Countable J][Countable E]
  (L₀:Lamps T J G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)(S:Lamps T I₀ G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)(M:Canopy.ShiftRows T E G P'.p ((X.family.path.levels.clock.op i per).ratio.parent ∘ o) R)

omit [Fintype V] [Countable J] in
private theorem negative (t : T) (U : Config G (X.family.side i per)) :
    bare L₀.shade t U = -bare L₀ t U := by
  unfold WilsonRootedKioskOccupiedSlip.bare
  rw [← tsum_neg]
  apply tsum_congr
  intro j
  ext m
  simp only [Lamps.shade, Pi.neg_apply, Poly.part_send, Poly.part_neg]
  split <;> simp

omit [Fintype V] [Countable J] in
private theorem gross {w : V → ℝ} {B : ℕ} {a c : ℝ} (h : Gross L₀ w B a c) :
    Gross L₀.shade w B a c := by
  obtain ⟨f,nonnegative,all,paid⟩ := h.before
  refine ⟨f,nonnegative,?_,paid⟩
  intro j t U
  simpa only [Lamps.shade, Pi.neg_apply, norm_neg] using all j t U

theorem deposited (live:i<N)
    (fineView:P.eval=(X.family.path.rep N per (i+1)).eval)
    (temperature:P.beta=(X.family.path.rep N per (i+1)).beta)
    (coarseView:P'.eval=(X.family.path.rep N per i).eval)
    (outputBeta:P'.beta=(X.family.path.rep N per i).beta)
    (point:P'.p=(X.family.path.rep N per i).p)
    {oldRegular newRegular oldSlip newSlip:ℝ}
    (old:S.Paid weights P'.p.B P'.p.supportExponent oldRegular)
    (fresh:L₀.Paid weights P'.p.B P'.p.supportExponent newRegular)
    (existing:M.Budget weights P'.p.B (P'.p.supportExponent+1) oldSlip)
    (unmasked:Gross L₀ weights P'.p.B (P'.p.supportExponent+1) newSlip) (slack:0<s)(shrink:ℝ)
    (lines:∀t u,(Travel.raw cash eyes A weights grant pos slots bill pin).log t u=S.log t u+M.log t u)
    (forest:Tree.Forest (X.family.path.levels.clock.op i per).ratio):
    let h:=WilsonRootedKioskFreeRadius.radius shrink oldSlip newSlip s
    let u:=Stoop.radius weights h
    let O:=WilsonRootedKioskPostedPortfolio.residual (Travel.mid cash W eyes A weights grant pos slots cap bill pin)
      W.second L₀.shade (L₀.join S) M
    1 ≤ h ∧ shrink ≤ h ∧ O.Pays u P'.p.supportExponent (h⁻¹*(newRegular+oldRegular)) r ∧
    (∀t z,O.density t z=Poly.pass (bare L₀ t z)*
      (X.family.path.levels.clock.op i per).push (X.family.path.rep N per (i+1)).beta (A.density t) z) ∧
    (∀t z,(O.density t z).part R.quiet=((X.family.path.rep N per i).eval z:ℂ)) ∧
    P'.beta=(X.family.path.rep N per i).beta ∧ P'.p=(X.family.path.rep N per i).p:=by
  intro h u O
  have split (t : T) (U : Config G (X.family.side i per)) :
      (Travel.raw cash eyes A weights grant pos slots bill pin).log t U =
        L₀.shade.log t U + (L₀.join S).log t U + M.log t U := by
    rw [lines, Lamps.shade_log, Lamps.joinLog t U (fresh.sums P'.p.exponent_pos.le pos t U)
      (old.sums P'.p.exponent_pos.le pos t U)]
    abel
  have returned := WilsonRootedKioskPhysicalPostWhole.original X cash eyes W A weights grant pos slots cap bill pin
    L₀.shade (L₀.join S) M live fineView temperature coarseView outputBeta point (Lamps.joinPaid fresh old)
    existing (gross X L₀ unmasked) slack shrink split forest
  exact ⟨returned.1,returned.2.1,returned.2.2.1,
    fun t z => by simpa only [negative X L₀ t z,neg_neg] using returned.2.2.2.1 t z,returned.2.2.2.2⟩

end YM.Integration.WilsonMixedFreshMerger
