import YM.LocalLTE.Quay.Engine
import YM.Integration.FVA1Physical.Round2.QuayForecast

/-! Full physical rows and retained proposals selected jointly on the calibrated
history before the ray, tag, linear test and ordinary Wilson order. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Quay
open Function Finset Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations FVA2.CityHistory UVNext.CouplingReset
open Comparison.RG02 RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge PertExtension PertExtension.Chart
open Integration.FVA1Physical.Wilson PertExtension.Series.Tested PhysicalNext.Repeat.Roost
open scoped Classical BigOperators

variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D}
    (P : Bolt A) (r₀ : ℕ→ℕ)
    (Y : ∀ d j t,TransferData ((Labels.frames G).level d) (Issue.trail P) j t)
abbrev voiceBall {I : Type} (z : I→ℕ) (G : Gauge) :=
  {v : ∀ j,((frames G).level (z j)).Coeff // ∀ j,((frames G).level (z j)).coeffSize (v j)≤1}

def PricedLibrary (p d c : ℕ) : Prop :=
  ∀ (N n m : ℕ), m < N → r₀ 0 ≤ m →
  ∀ {I : Type} [Fintype I] [DecidableEq I] (B : Census I) (z : I→ℕ),
  Fintype.card I ≤ c → (∀ j,z j ≤ d) → (∀ j,r₀ (z j) ≤ m) →
  ∀ (_paths : ∀ i:ℕ, LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n))),
  ∃ (rows forecast : voiceBall z G → B.Mode → ∀ i, Coefficient ((frames G).level 0) ((Issue.trail P).S.side i n)),
    (∀ v s i, m ≤ i → ∀ hi : i ≤ N, ∀ U,
      (Bandage.Harmonics.vista (P:=P) (N:=N) (n:=n) B z v.val i hi U).part s =
      (rows v s i).density 0 (localSection G 0) ((Issue.trail P).rep N n i) U) ∧
    ∀ i, m ≤ i → ∀ (hi : i ≤ N) (T:Slices (Issue.trail P).levels n)
      (room:(traversal T hi).Room G) (tag:(traversal T hi).Tags)
      (u:Pins G ((Issue.trail P).S.side i n)) (Z:ChartRatio G), LocalRatio Z →
      ∀ (s:B.Mode) (L:ℂ →L[ℝ] ℝ) (r:ℕ),
      let H := Issue.trail P
      let C := YM.Family.mk H (Next.Foundations.hol G) (Labels.frames G) (Next.Foundations.localSection G) r₀ Y
      let g := Pert.Asymptotics.regulatorRun C N n N
      let U := expLinks G _ (g • u)
      let β := if i=N then (H.rep N n N).beta else (H.rep N n (i+1)).beta
      ∃ K:ℝ, 0≤K ∧ ∀ v:voiceBall z G, flags (H.rep N n i).p.threshold U=∅ →
        let E := scalarWilsonBank (traversal T hi) room tag u (actualOffset C n N i) Z
          (L ∘ fullProduct (centeredBatch P N n z v.val).wavelengths s.val)
        ‖L ((forecast v s i).exponentialEntry 0 (localSection G 0) (H.rep N n i) U)-peval E r g‖ ≤
          ‖L‖ * PhysicalNext.Repeat.Legato.Spool.powerR p β + K*g^(r+1)

variable {R:Factor A} {a:ℕ→ℝ} {W:Bid.Worth} {l q M p₀ j K d c ι p:ℕ} {κ e:ℝ}
    (U:Bandage.Harmonics R a W P l) {Hₓ:Spool.Heights}
    (hr:Spool.Terms R.shape κ p₀ j l q M K e A.delay Hₓ)
    (hp:East.stagnate q 500<l) (hR:∀ i j,(R.target i j).halo=500)

theorem library_price (lib:Bandage.Harmonics.Library U hr hp hR r₀ Y p d c ι)
    (ok:YM.Family.Makes (YM.Family.mk (Issue.trail P) (Next.Foundations.hol G)
      (Labels.frames G) (Next.Foundations.localSection G) r₀ Y)) : PricedLibrary P r₀ Y p d c := by
  intro N n m hm h₀ I _ _ B z card cap fits paths
  choose F _schedules reads using fun v:voiceBall z G =>
    (lib N n m hm h₀ I B z v.val paths card cap fits v.property).1
  refine ⟨fun v s i=>(F v s i).X,fun v s i=>proposal (P:=P) i (F v s i) K,?_,?_⟩
  · exact fun v s i lo hi U₀=>((reads v i lo hi).2 s).story U₀
  · intro i lo hi T room tag u Z hZ s L r H C g U₀ β
    obtain ⟨J,hJ,price⟩ := forecast_wilson P B z r₀ Y T hi room tag u s L ok hZ r
    refine ⟨J,hJ,fun v hgood=>?_⟩
    exact price v.val v.property _ _ _ _ _ _ _ _ _ ((reads v i lo hi).2 s) hgood
end YM.Integration.FVA1Physical.Round2.Quay
