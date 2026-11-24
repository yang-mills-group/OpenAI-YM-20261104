import YM.Qlocal.Money
/-!
 Output rents BEFORE vs after restoration. Actual relativeBudget uses exactly
 these cash/toll factors; κ divisor included.K moments never integrated in
 this estimate. Quiet still on the original Shelf. Includes any step of
 Trip and, on close windows, any (finite coupling power fixed once) strength
 request after Λ.Hi shells.Non-final layout.Prom.Focus Prop Semilir.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Program.Certificate
open Function Filter Set Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open Marker MeasureTheory Extra.Trajectories Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms
open Progress.DirectedRecipe ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Metric Height Roof Input Org Supply Pane Slide
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff BigOperators YM.Qlocal.Payload
open AllOrder Transit Transit.WheelP Floe.Step.PlanV
open Merge Switch Spectrum UniformPays Publishing Emissions Payload Provisional Footprint StageArt
open RGComparison01 RGComparison01.Pledge
open Leasing Integration Integration.LocalComparison Integration.RiderTastePresentation
open Hull Camp Frigus Time Coat
variable {Ω ι V : Type} [DecidableEq V] {B:Marker.Census V} {G:Gauge}{X:Metals G}{D:Rolls X.p}
    {Δ:ℕ→Prop}{A:Alloy X D}(F:Factor A){m k p N j k' z n l : ℕ} {δ r θ u v w E C ℓ: ℝ}
local notation "a"=> A.B.a
set_option quotPrecheck false
variable (h:G.Simple) (η:ℕ→ℝ)(H T:ℕ→ℕ)
variable (Y₀:Org.Bolt A) (Q:Camp F η H T) (hT:Tendsto T atTop atTop)
-- Path supply:
variable {R: (i:ℕ)→ RG.Rep G (A.B.a.S.side i p)}{P : ℕ→Floe.Layout G}{Γ : ℕ→ Floe.Pace.Coin}(p₀:JourneyK A F Y₀ P Γ z N p k R) -- `JourneyK`
    (o:(i:ℕ)→V→ Site (A.B.a.S.side i p)) (s:(i:ℕ)→ V→Support (A.B.a.S.side i p)) (u: V→ℝ) (c:B.Mode→ℝ) (j:ℕ)
local notation "S"=> A.B.a.clock.op m p
local notation "Ψ"=> R (m+1)
local notation "Cw"=> hard a m
local notation "β"=> (R (m+1)).beta
local notation "Q'"=> Time.quoteHard (a) m F.book (R (m+1)).beta
local notation "u!"=> shift (Q.scale m j) u
local notation "d★"=> Hull.divisor a m
variable [Fintype V] [Nonempty Ω][Nonempty V] (hC:Spirit c)(hu:∀ i,0 < u i)
    (Y:Taste Ω (o j) (R j) B)(M:Protocol A.B.a p Ω B R o)(W:(m:ℕ)→Taste Ω (o m) (R m) B)
    (hw: Trip Q o s u c j Y M W z) (ht:Agenda (A:=A) o s z j)(hj:j≤N)
local notation "𝔓"=> rent u c
abbrev Rank (k:ℕ) (B:Marker.Census V) := ∀ i:B.Mode,i.val.card ≤ k
include hw hC hu p₀ hj Q
lemma lit (h1:z ≤ m)(hb:m < j) (hR:Rank l B) : ∃ K:ℝ, 1 ≤ K ∧ K=Q.scale m j ∧
  (Peak (R m) (o m) (W m) (rent u c) (R m).p.supportExponent (K^l) ((K^l)*hardcap (a) T m)) := by
 obtain ⟨hp,hd⟩:= hw.move m h1 hb; let v:=Q.scale m j; have hz:= Q.scaled m j; have he:= zero_lt_one.trans_le hz; refine ⟨v,hz,rfl,?_⟩
 have hQ : Peak (R m) _ (W m) (rent u c) (R m).p.supportExponent (v^l*1) (v^l*Q'):= Peak.transfer (fun i=> (rent_spend hu hC.fresh i).le) (pow_pos he l).le hp (fun i _=> recover _ hC hu hz hR i)
 rw [mul_one] at hQ; exact hQ.loosen le_rfl (mul_le_mul_of_nonneg_left (Q.lease_stand p₀ h1 (hb.trans_le hj)) (pow_pos he l).le)

lemma stable (hm:z ≤ m)(hb:m < j)(t:ℕ) (hR:Rank t B) (k:ℕ) (d:ℝ) (hx:Q.scale m j ^ t ≤ soft d (R (m+1)).beta)
    (he: Q.scale m j ^ t * hardcap (a) T m ≤ hard (a) m * Coat.gStep (R (m+1)).beta^k):
   (Peak (R m) (o m) (W m) (rent u c) (R m).p.supportExponent (soft d ((R (m+1)).beta)) (hard (a) m * Coat.gStep β ^k))∧
   Nonempty (RelativeBudget (R m).p (W m) u d★ c ((Real.exp 1+1)*soft d β) (d★*Coat.gStep β ^ k)):= by
 obtain ⟨K,-,hKv,hV⟩:= lit F η H T Y₀ Q p₀ o s u c j hC hu Y M W hw hj hm hb hR
 let p':= (R m).p; rw [hKv] at hV; have hF:= hV.loosen hx he; have heV:=Peak.relative (T:=W m) (f:=c) (P:=R m) le_rfl (luminous a m).1 hu hC.fresh hF hC.light; refine ⟨hF, ?_⟩; rw [show (Cw*Coat.gStep β ^ k)/d★=(d★*Coat.gStep β ^k) from ?_] at heV; exact heV
 have h0:= luminous (a) m; -- ambiguity.Case can avoid rewriting divisor abbrev
 field_simp [h0.1.ne']; rw [h0.2.2]; ring
-- Usage: before ANY markers/custom allocation.Ness.
omit hw p₀ hC hu hj -- order any shape and p.F.Engine
include h hT
structure ShowT (Q:Camp F η H T) (i l k :ℕ)(d:ℝ):Prop where
 costs : ∀ j≥i,Hull.Close A.B.a i j→∀ x∈ band A.B.a (i+1), Q.scale i j^l ≤ Hull.soft d x ∧ Q.scale i j^l*Frigus.hardcap A.B.a T i ≤ Hull.hard A.B.a i*Coat.gStep x ^ k
lemma supplied (k l:ℕ)(d:ℝ)(hp:0<d) : ∀ᶠ m in atTop, ∀ i≥m, ShowT F η H T Q i l k d:= by
 obtain ⟨t,hT⟩:= eventually_atTop.mp ((Hull.bagged F Q h hT l k).and (Hull.looming F Q h hp l)) -- argument order
 exact (eventually_ge_atTop t).mono fun m ht i hx=> ⟨fun j hj hh x he=> ⟨(hT i (by omega)).2 j hj hh x he,(hT i (by omega)).1 j hj hh x he⟩⟩
omit h hT
include hu hj hC hw p₀
lemma growing (m0:ℕ) (hr: ShowT F η H T Q m l m0 δ) (he:m < j)(hi : z ≤ m)(hx : Rank l B)(hh: Hull.Close (a) z j) :
   (Peak (R m) (o m) (W m) (rent u c) (R m).p.supportExponent (soft δ ((R (m+1)).beta)) (hard (a) m * Coat.gStep β ^m0))∧
   Nonempty (RelativeBudget (R m).p (W m) u d★ c ((Real.exp 1+1)*soft δ β) (d★*Coat.gStep β ^ m0)):= by
 have hκ : β∈ band a (m+1):= (p₀.1.walk (m+1) (by omega) (by omega)).beta.symm ▸ (Y₀.sticks N p|>.prices (m+1) (by omega) (by omega)).2
 have hf:= hr.costs j he.le (Hull.close_shrink hh hi) _ hκ
 exact stable F η H T Y₀ Q p₀ o s u c j hC hu Y M W hw hj hi he l hx m0 δ hf.1 hf.2
end YM.Qlocal.Program.Certificate
