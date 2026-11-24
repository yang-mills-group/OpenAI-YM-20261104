import YM.Integration.WilsonOriginalPublicNodalBufferedCellRow
import YM.Integration.WilsonPositionProgramTrialPublicCellHull

/-! Reindex the actually received torus film on a uniform finite box, retaining the true subcell jet in each row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalBufferedCellFilm
open Function Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Cirrus MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open PhysicalNext.Repeat.Legato RegulatorIR.Profiles
open WilsonIndependentSpoutRosterCashier (complex)
open WilsonIndependentSpoutPhysicalHomes (filmAt load)
open WilsonOriginalPublicNodalBufferedCellRow (Source Stamps Frames gain bank profile)
open WilsonPositionProgramTrialPublicCellHull (hull)
open WilsonIndependentPublicReportComplex (apply row)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)
  (cut:∀i,d i<D i)(Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)
  (y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→ CellR)
abbrev Sites:=Fin (n+1)→Finset Cover
abbrev Seats (H:Sites (n:=n)):=(i:Fin (n+1))→(H i)×Alma (Frames R d i)
abbrev Disp (n:ℕ):=Fin (n+1)→Point4

def entry {H:Sites (n:=n)}(c:Source R d)(ξ:Disp n)(u:Seats R d H):ℂ⟦X⟧:=
  PowerSeries.C (gain R d D cut T x y σ sp o ξ (fun i=>(u i).1.val) (fun i=>(u i).2):ℂ)*
    bank R W kind d Y c (fun i=>(u i).1.val) (fun i=>(u i).2)

def full (H:Sites (n:=n))(c:Source R d)(ξ:Disp n):ℂ⟦X⟧:=
  ∑u:Seats R d H,entry R W kind d D cut Y T x y σ sp o c ξ u

def paper (c:Source R d)(ξ:Disp n):ℂ⟦X⟧:=
  let φ:=fun _:Unit=>profile D T x y σ sp o ξ
  ∑u:WilsonIndependentSpoutPhysicalHomes.Visits R d D φ (fun _=>x) (fun _=>y) (fun _=>o) (),
    complex (load R d D cut φ (fun _=>x) (fun _=>y) (fun _=>o) () c (fun _=>1) u)*
      filmAt R W kind d D φ (fun _=>x) (fun _=>y) (fun _=>o) (fun _=>Y) () u

theorem original (c:Source R d)(xp:∀i,0<x i)(ξ:Disp n)(bounded:∀i,‖ξ i‖ ≤ 1):
    paper R W kind d D cut Y T x y σ sp o c ξ=
      full R W kind d D cut Y T x y σ sp o (fun i=>hull (T i) (x i) y σ (o i)) c ξ:=by
  let φ:=profile D T x y σ sp o ξ
  let S:=fun i=>VisitsT (φ i) (x i) y (o i)
  let H:=fun i=>hull (T i) (x i) y σ (o i)
  have sub (i):S i⊆H i:=WilsonPositionProgramTrialPublicCellHull.original (T i) (xp i) y σ sp (o i) (ξ i) (bounded i)
  let inc:Seats R d S→Seats R d H:=fun u i=>(⟨(u i).1.val,sub i (u i).1.property⟩,(u i).2)
  have injective:Injective inc:=by
    intro a b eq
    funext i
    exact Prod.ext (Subtype.ext (congrArg (fun t:Seats R d H=>(t i).1.val) eq))
      (congrArg (fun t:Seats R d H=>(t i).2) eq)
  let F:=entry R W kind d D cut Y T x y σ sp o (H:=H) c ξ
  have genuine:paper R W kind d D cut Y T x y σ sp o c ξ=∑u:Seats R d S,F (inc u):=by
    unfold paper
    dsimp only
    apply sum_congr rfl
    intro u _
    exact WilsonOriginalPublicNodalBufferedCellRow.original R W kind d D cut Y T x y σ sp o c ξ u
  rw [genuine]
  change (∑u:Seats R d S,F (inc u))=∑u:Seats R d H,F u
  rw [←sum_image (f:=F) (g:=inc) (s:=univ) (fun a _ b _ eq=>injective eq)]
  apply sum_subset (subset_univ _)
  intro u _ missing
  have gone:∃i,(u i).1.val∉S i:=by
    by_contra! allIn
    apply missing
    let old:Seats R d S:=fun i=>(⟨(u i).1.val,allIn i⟩,(u i).2)
    exact mem_image.mpr ⟨old,mem_univ _,rfl⟩
  obtain ⟨i,absent⟩:=gone
  have dull:wheelC (x i) y (u i).1.val (φ i).ψ (o i)=0:=by
    by_contra live
    exact absent ((visiting (xp i)).mpr live)
  have zero:gain R d D cut T x y σ sp o ξ (fun i=>(u i).1.val) (fun i=>(u i).2)=0:=by
    apply prod_eq_zero (mem_univ i)
    change drumB (d i) (x i)*jewelBloom (cut i) (u i).2 (wheelC (x i) y (u i).1.val (φ i).ψ (o i))=0
    rw [dull,map_zero,mul_zero]
  unfold F entry
  rw [zero]
  simp

theorem continuous_full (H:Sites (n:=n))(c:Source R d)(q:ℕ):
    Continuous fun ξ:Disp n=>coeff q (full R W kind d D cut Y T x y σ sp o H c ξ):=by
  simp only [full,map_sum]
  apply continuous_finsetSum
  intro u _
  exact WilsonOriginalPublicNodalBufferedCellRow.continuous_row R W kind d D cut Y T x y σ sp o c
    (fun i=>(u i).1.val) (fun i=>(u i).2) q

theorem measured (E:Set (Disp n))(xp:∀i,0<x i)(inside:∀ξ∈E,∀i,‖ξ i‖ ≤ 1)
    (c:Source R d)(clock:Feeds)(pole q:ℕ):
    ContinuousOn (fun ξ=>coeff q (apply clock pole (paper R W kind d D cut Y T x y σ sp o c ξ))) E:=by
  let H:=fun i=>hull (T i) (x i) y σ (o i)
  have smooth:Continuous fun ξ=>coeff q (apply clock pole (full R W kind d D cut Y T x y σ sp o H c ξ)):=by
    simp only [WilsonIndependentPublicReportComplex.coefficients]
    apply continuous_finsetSum
    intro i _
    exact (continuous_full R W kind d D cut Y T x y σ sp o H c i).mul continuous_const
  apply smooth.continuousOn.congr
  intro ξ hξ
  exact congrArg (fun f:PowerSeries ℂ=>coeff q (apply clock pole f))
    (original R W kind d D cut Y T x y σ sp o c xp ξ (inside ξ hξ))

theorem integrable (E:Set (Disp n))(compact:IsCompact E)(xp:∀i,0<x i)(inside:∀ξ∈E,∀i,‖ξ i‖ ≤ 1)
    (μ:Measure (Disp n))[IsFiniteMeasureOnCompacts μ](c:Source R d)(clock:Feeds)(pole q:ℕ):
    IntegrableOn (fun ξ=>coeff q (apply clock pole (paper R W kind d D cut Y T x y σ sp o c ξ))) E μ:=
  (measured R W kind d D cut Y T x y σ sp o E xp inside c clock pole q).integrableOn_compact compact

end YM.Integration.WilsonOriginalPublicNodalBufferedCellFilm
end
