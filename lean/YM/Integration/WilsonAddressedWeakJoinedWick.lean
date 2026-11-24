import YM.Integration.WilsonAddressedWeakFiledHeat
import YM.Integration.WilsonAddressedWeakActualExaminer
import YM.MergeProof.West.Esme

/-! The connected finite Gaussian hearing of the actual enrolled displaced fields.
Its independent labels and compact placement set are chosen before the regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakJoinedWick
open Function Set Filter RG Lattice Wilson Marker Cells Next.Rank
open RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu Source
open Trace.Physical Spindle Configuration Normal Rise Perch Glimmer LiftMark Beamer Station Atlas Tariffs Tapes MvPolynomial
open Next.Rank.Glyph Next.Rank.Exponential Next.Rank.Read Next.Rank.Ship Next.Rank.Tapes.West Next.Rank.Ribbon
open WilsonAddressedWeakDisplacedWick
open scoped Classical Topology BigOperators
variable {G:Gauge} {C:Family G} {d k p n b:ℕ}

theorem shifted (Y:AtlasData G C.S p) (wide:4*b≤wood C.path.levels k) (h:invariantAt (C:=C) k (wood C.path.levels k) p Y)
    (W:poly (slotC G b)) (s:Cover) :
    lifted Y W s k wide=rename (fun x:trimV (wood C.path.levels k) G=>body (P:=C.S) (k:=k) (p:=p) s x.val)
       (milk (-(control Y (k:=k) s (wood C.path.levels k))) (WilsonAddressedWeakDisplacedWick.heat wide Y W)) := by
  rw [h s,WilsonAddressedWeakDisplacedWick.heat,warms]
  have opp {Z:Type} (K:Normal.Symmetric Z): -K+K=0:=by
    apply Normal.Symmetric.ext;funext i j;exact neg_add_cancel _
  rw [opp,Normal.froze]
  rfl

variable (R:Run G) {g:Fin n→ℕ} (h:∀ i,g i≤d) (v:(i:Fin n)→R.family.label (g i))
local notation "A" => R.family.path.levels
local notation "F" => R.family

include h

theorem original (simple:G.Simple) (exam:Tapes.Panel d) (K:Set (Points n)) (hc:IsCompact K) (good:K⊆conf n) :
    ∀ᶠ k:ℕ in atTop,∀ x:Points n,∀ p:ℕ,
    let ξ:=exam.bag ((A).clock.J k)
    let s:=clim (A) k
    let c:=Station.choose (A) ξ.band k x
    let l:=before (A) ξ.band k
    Station.tested (A) ξ.band k x∈K →
    ∀ (fit:Station.Fit (A) ξ.band k x) (_:Allowed (A) ξ.band k)
      (Y:AtlasData G (F).S p) (_:Hail F k p ξ.taylor Y) (_:invariantAt (C:=F) k (wood (A) k) p Y)
      (_:Wall.Vantage (A) d k p n ξ.taylor ξ.band Y)
      (sizes:Fin n→ℕ) (wide:∀ i,4*sizes i≤wood (A) k)
      (W:(i:Fin n)→poly (slotC G (sizes i))),
    (∀ i,(W i).totalDegree≤ξ.taylor) →
    (∀ i,let F₀:=(F).labels.level (g i)
         coin (W i)≤(2*bill (5/8) s)*((2*2^leash F₀*F₀.coeffSize (v i))*bill (exam.arc*g i+(leash F₀:ℝ)) s)) →
    (∀ i,WilsonThermometerWeakGroupCoordinate.contracted R (g i) (wide i) Y (W i)=expose ((F).labels.level (g i))
      (Price.weightTag F (g i) (Station.mag (A) ξ.band k) (v i))) →
    ∀ y:Chamber G (F).S (middle (A) ξ.band k) p→ℝ,Atlas.Wind (A) y (fraction n ξ.taylor s) →
       ‖t_cum (track Y) (fun i=>lifted Y (W i) (c i) k (wide i)) l y-Ship.targets F (Atlas.jointX v) fit‖+
         bill (-3/2) s ≤ bill (-31/32) s := by
  have six:6≤exam.arc:=by linarith only [exam.huge,Nat.cast_nonneg (α:=ℝ) d]
  have pos:0<exam.arc:=by linarith
  have enough(i):Atlas.saves F (g i)+3≤exam.arc:=by
    linarith only [Tapes.savings F (g i),exam.huge,show (g i:ℝ)≤(d:ℝ) from Nat.cast_le.mpr (h i)]
  filter_upwards [West.mural_cast h v hc good R.makes simple exam.arc six enough exam.θ,
      offered h v simple exam.arc pos enough exam.θ,
      eventually_all.mpr fun i=>WilsonAddressedWeakFiledHeat.paid (C:=F) simple (v i) exam.arc exam.θ]
      with k walls purchase hats x p ξ s c l member fit allowed Y hail invariant geometry sizes wide W degrees rates fields y wind
  have date:ξ.band=exam.arc:=exam.factor _
  have order:ξ.taylor=exam.θ:=exam.stable _
  rw [←date,←order] at walls
  rw [←date,←order] at purchase
  rw [←date,←order] at hats
  let P i:=WilsonAddressedWeakDisplacedWick.heat (wide i) Y (W i)
  let V i:=lifted Y (W i) (c i) k (wide i)
  have salary(i):coin (P i)≤bill (ξ.band*g i+Atlas.saves F (g i)) s ∧ (P i).totalDegree≤ξ.taylor :=
    hats i (wide i) Y hail (W i) (degrees i) (date ▸ rates i)
  have packed:=purchase P (fun i=>(salary i).1) (fun i=>(salary i).2) fields
  have balcony:=walls.merry x member
  have bell:Atlas.Bell (A) Y d ξ.taylor fit:=(walls.replies x member fit allowed).2 p Y geometry
  have ex:Expands (t_cum (track Y) V l y) (Answer Y c l P (fun i=>(y i:ℂ))):=by
    have eq:spunW (track Y) V l y=Answer Y c l P (fun i=>(y i:ℂ)):=by
      ext z
      apply Eq.symm
      change _ = text y (shelve (track Y) l (∏ i∈z.val, V i))
      rw [Tapes.forecast]
      dsimp only [V,P]
      simp_rw [shifted Y _ invariant]
      rfl
    exact eq ▸ expanders (track Y) V l y
  exact balcony.mind _ _ _ ex (Read.cumulative F _ (Atlas.jointX v) (Ship.fitting fit))
    (fun z=>sampled h v fit P bell y wind packed (balcony.pends fit) z)

end YM.Integration.WilsonAddressedWeakJoinedWick
