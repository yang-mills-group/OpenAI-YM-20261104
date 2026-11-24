import YM.Integration.WilsonOriginalPublicTrialPhaseTerminal
import YM.Integration.PricedWholeProduct

/-! Every replicated finite fitted K word is integrable on the inherited law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseWhole
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Push Marker Extra.Histories
open MergeProof Accent Extra.Multi Cells OPE.Therm PhysicalNext.Repeat.Legato Push.GridApprox
open OPE.Therm.ReplicaChessboard WilsonOriginalPublicTrialPhaseTrace WilsonOriginalPublicTrialPhaseTerminal
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) {N p K u J:ℕ}
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "H" => (C).path
local notation "V" => Site ((C).side J p)

theorem continuous_file {I:Type} [Fintype I] (d:I→ℕ)(z:I→Site ((C).side K p))(v:∀i,(C).label (d i)) :
    Continuous (word R (N:=N) d z v):=by
  apply continuous_finsetProd _ 
  intro i _
  exact continuous_const.add (((C).localSection _).continuous_places _ _)

theorem whole {I:Type} [Fintype I] (d:I→ℕ)(z:I→Site ((C).side K p))(v:∀i,(C).label (d i))
    (jk:J≤K)(live:K≤N)(a:ℂ):Integrable (opening R (N:=N) jk (fun U=>word R (N:=N) d z v U-a))
      (prior G ((C).side K p)):=by
  let T:=tilesAt (C).S p jk
  have cov(i:T.Cell):Continuous (T.copy i (fun U=>word R (N:=N) d z v U-a)):=by
    have h:=((continuous_file R (N:=N) d z v).sub (continuous_const (y:=a))).comp
      (continuous_pull (G:=G) (T.omega i) (T.translateBy i))
    unfold Tiling.copy
    by_cases sign:T.hand i
    · simpa only [if_pos sign,Function.comp_def,Pi.sub_apply,Pi.star_apply] using h.star
    · simpa only [if_neg sign,Function.comp_def,Pi.sub_apply] using h
  exact (hatCont (C) K p _ cov (RG02.Actual.eval_cont R.makes.wilson live) (Stock.census V)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem original {I:Type} [Fintype I] (d:I→ℕ) (z:I→Site ((C).side K p)) (v:∀i,(C).label (d i))
    (ju:J≤u) (uk:u≤K)(live:K≤N)(r:ℕ)
    (fit:∀i,window (z i) (stencilRadius (C) (d i))⊆window 0 r)
    (space:room (A) J K r) :
    let jK:=ju.trans uk
    let M:=word R (N:=N) d z v
    let a:=actualTransport (C) (N:=N) M uk 1
    let X₀:=fun U=>M U-a
    ∀
      (F₀:V → Config G ((C).side u p)→ℂ)
      (F₁:V→Box ((C).side u p) → Config G ((C).side u p)→ℂ)
      (o:V→Site ((C).side u p)) {w b h f:ℝ},0<w →
      Served ((H).rep N p u) F₀ F₁ (arrival R (N:=N) jK uk X₀) o (fun _=>w) ((A).budget u).supportExponent f →
      Vault (fun _:V=>w) F₀ F₁ b h →
      ‖(∫U,M U ∂scene (H) N p K)-a‖≤
        Real.exp (((C).S.a J/(C).S.a u)^4*Vac.treasury (A) u+b+h+2*f)/w :=by
  intro jK M a X₀ F₀ F₁ o w b h f hw served vault
  exact WilsonOriginalPublicTrialPhaseTerminal.original R d z v ju uk live r fit space
    (whole R d z v jK live a) F₀ F₁ o hw served vault

end YM.Integration.WilsonOriginalPublicTrialPhaseWhole
