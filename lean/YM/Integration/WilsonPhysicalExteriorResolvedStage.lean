import YM.Integration.WilsonPhysicalExteriorResolvedReadout
import YM.FVAAlt2.Rocket.Export

/-! The true forest/regulator on the original selected Wilson Run:
separation only from below, and unwrapped addresses polynomial in the
actual inverse spacing. Independent far physical markers may escape.
The finite field registry, notebook, local correction and clock are fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolvedStage
open YM.RegulatorIR YM.RegulatorIR.FVAAlt2 YM.RegulatorIR.FVAAlt2.Rocket YM.RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorResolvedReadout WilsonPhysicalExteriorResolvedCutoff WilsonPhysicalExteriorUVStory
section
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Topology Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain RegulatorIR.Profiles Sources Labels Source Momentum
open Oracle Atlas Epoch Calibration Kick YM.FVAAlt2
open MS MS.Menus MS.Dial MS.Land MS.Vista MS.Fleet MS.Tide MS.Orbit MS.High MS.Port
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}{u a b p r:ℕ}{M:X→ℕ}{n:Page M→Side}{G:Gauge}
variable (S:Oracle.Circuit M n){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P: Patch,P.Branches K G) {B:Epoch.Marked M}
variable {g:G.ColorIndex}{γ c₀:ℝ}(F: Calibration.Tent M){x:X→Room}{L:Meter X}
local notation "AΘ"=> S.payroll Y G Z (sheet F)
local notation "Σ'"=> S.dialect Y G Z (sheet F)
local notation "η"=> native M
local notation:max "P_" w:max => Page.opening M w
variable (J:Choice M)[LinearOrder I][Fintype I]
variable {Λ:Frames G}{H:Hol G} (R:Lobby.Registry Λ H) (T:MS.Dial.Trial X I)(μ:ℝ){Ξ:MS.Local.Physical.Deck G}(c:I→ Rake.Label Ξ)(K₁:MS.Land.Prescription Ξ)
local notation:max "Θ" i:max=> T.profile.θ i
set_option quotPrecheck false
local notation "Θ'"=> T.profile.θ
local notation "ε'"=> fun i=> Real.exp (- Θ i )
local notation "∂'"=> interpreted S Y Z F J R T μ c K₁
variable (hq:Atlas.SatisfiesQ G Y S Z B p u γ)(hver: Calibration.Notebook S Y G Z g (native M) F p) (hc:∀ w,B.peak (Page.opening M w)=0) (hP:∀ w,S.l (Page.opening M w)=1)
variable {D:Precision.ChartRatio G}(hD:Precision.LocalRatio D)(hL:OfAge B L)(hN:∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v)(hg:G.Simple) (hb:quantum 1 0 ≤u)(hp:0<c₀)(ht:(S.dialect Y G Z (sheet F)).cushion c₀ x)
variable (l:Filter X)(h:Pace S J T.profile.θ l L) (Hn: n ∘ Page.opening M= MS.Orbit.dimT T.side) -- can't notation in variable type
variable (h₀:∃ y,Nearest x L y)(hτ:∀ i,Nearest x L fun w=> Zpose T w i)
include hq hver hc hP hD hL hN hg hb hp ht h Hn h₀ hτ
variable {A:Booked Ξ}(U:MS_Data G A)(hK:TaylorOKPl U (Lobby.Table R Ξ) K₁) (hT:Domain T l μ)
include hT hK
theorem stage (he:r≤p): PeakT.twin l T.profile mildG (∂' r) (fun i=> Dial.tour U c μ (testP T i) Finset.univ r):=by
    obtain ⟨H,H'⟩:= measured D R K₁ c U hD hT hg hK r
    refine ⟨H,?_⟩
    have hx:= PeakT.plus (elected S Y Z F J R T μ c K₁ hq hver hc hP hD hL hN hg hb hp ht l h Hn h₀ hτ he mildG mild_p) H'
    rwa [sub_add_sub_cancel ..] at hx
end

section
open Function Set Filter MeasureTheory Topology Real
open Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Ledger.Sky Taping Atlas Spatial
open MS MS.Plane MS.Dial MS.Orbit MS.Tide MS.Vista MS.Fleet MS.Land MS.High MS.Rake
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}(T:Track X){G:Gauge}
set_option quotPrecheck false
variable [LinearOrder I][Fintype I]
variable (μ:ℝ)(U:X→ Cover)(W:I→ X→ Cover)(l:Filter X)
local notation "F"=> T.PoseT μ U W
local notation "Ω"=> T.Θ
local notation:max "P₀" x:max => Motion.slide 1 (U x)
omit [LinearOrder I] [Fintype I] in
theorem finite_positions (hp:Reach (F).profile W) (i:I) : Kick.Nearest (fun x=>P₀ x) T.lumber fun w=> Zpose F w i:=by
    obtain ⟨C,hC,d,H⟩:=hp i; have hx(x): dist (P₀ x) (Motion.slide 1 (Zpose F x i))= ‖Tone.embed ( W i x )‖:=by
        rw [show Zpose _ x i= U x+W i x from rfl,map_add,dist_comm,dist_self_add_left]; apply congr_arg _; exact funext fun z=> one_mul _
    refine ⟨ ((Poly.standard _ (ENNReal.ofReal_ne_top (r:=C))).mul ((Poly.roof _).powQ d)).mono fun w=> ?_⟩
    change ENNReal.ofReal (dist _ _)≤_; rw [hx]; refine (ENNReal.ofReal_le_ofReal (H w)).trans_eq ?_; rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_pow (Real.exp_pos _).le]; rfl
end

section
open Function Set Filter MeasureTheory Topology Real
open Lattice RG Precision Gauge
open Oracle Epoch Calibration Calibration.Notebook Rocket Uniform Binding Diagram Ledger Ledger.Sky Taping Atlas
open YM.FVAAlt2
open PhysicalNext.Repeat.Legato -- FVAAlt2 names overlap
open MS MS.Dial MS.Tide MS.Orbit MS.Port MS.Vista MS.Fleet MS.Land MS.Rake MS.Local.Physical
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type} {G:Gauge}{K:KernelChoices}
variable (Y:Oracle.Program K)(Z:∀ Q:Patch,Q.Branches K G)(C:Run G)
variable (SP: Contract C Y Z) (stamp:X→ℕ)(H:∀ x,SP.floor Y Z C ≤ stamp x)
local notation "T₁"=> SP.profile Y Z C stamp H
set_option quotPrecheck false
variable (F: Tent (SP.profile Y Z C stamp H).entire) {g:G.ColorIndex} (μ:ℝ)(p:ℕ)
local notation "B"=> (T₁).desk
local notation "Θ₀"=> (B).dialect Y G Z (sheet F)
open Integration.RunFormalChain
local notation "R"=> basisR C
variable [LinearOrder I][Fintype I]
variable {A: Local.Physical.Deck G}{S: Booked A} {T: MS_Data G S} {T' : Prescription A}
variable {Q: ChartRatio G}(D:I→ Rake.Label A) {l:Filter X}
variable (hver: Calibration.Notebook (SP.profile Y Z C stamp H).desk Y G Z g (native (SP.profile Y Z C stamp H).entire) F p)(hG:G.Simple)
    (hξ: Tendsto stamp l atTop)(hp:∀ x,p≤ stamp x) (hT: TaylorOKPl T (Lobby.Table (basisR C) A) T')
local notation "he'"=> SP.profile Y Z C stamp H
variable (U:X→ Cover)(W:I→ X→ Cover) (hU:(SP.profile Y Z C stamp H).VenueT U)
-- arbitrary geometric test. path animation one p announced; TV.Never reset + cc
local notation "xM"=> (T₁).PoseT μ U W
include hver hG hξ hp hT hU
theorem original (hz:Reach (xM).profile W)(hm:Resolved (xM).profile (info W))(k:ℕ)(he:k ≤ p): PeakT.twin l (xM).profile mildG (physicalCover Y Z C SP stamp H F μ D U W T' k) (fun x=> tour T D μ (testP xM x) Finset.univ k):=by
 obtain ⟨hb,hh,h'⟩:=hU.2.2
 let hL:=SP.batch_r Y Z C stamp H hξ
 exact stage B Y Z F (T₁).stop R xM μ D T'
     (SP.marks Y Z C stamp H p hp) hver (T₁).peak_point (T₁).opens
     (D:= C.metals.O) ( C.alloy.B.ratio ) -- binder `D:=` not Q
     ((T₁).credits Y Z) ⟨ 8,fun w=>by rw [(T₁).shut]; exact le_rfl ⟩ hG (le_max_left ..) hh
     (show (Θ₀).cushion hb (fun x=> Motion.slide 1 (U x)) from h') l ((T₁).era hL) (funext fun i=> ((T₁).payments i).symm) ⟨ U,(T₁).idNear U⟩ (finite_positions (T₁) μ U W hz) T hT ⟨hz,hm,fun _=>rfl,(T₁).θ_runs hL,(T₁).super l hL,hU.1,hU.2.1⟩ he
end

end YM.Integration.WilsonPhysicalExteriorResolvedStage
