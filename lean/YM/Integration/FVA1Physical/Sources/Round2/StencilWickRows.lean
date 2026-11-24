import YM.Integration.FVA1Physical.Wilson.PurchasedColumn
import YM.Integration.FVA1Physical.Wilson.StencilTicket
import YM.RGComparison.Core16.Lumen.Fable

/-! A polynomial in the finitely many physical log-link coordinates actually seen
by the mixed canonical stencil. Trunk coordinates are fixed to zero before any period
or Schur covariance is chosen. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior Marker Multi
open FormalOPE.RG10.MultiGauge RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FVA2.CityHistory MSbar MSbar.Lis MSbar.Whisk MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bakery MSbar.Bakery.Film MSbar.Cacao YM.Integration.FVA1Physical.Wilson Next.SectorChange
open scoped Classical Topology BigOperators ContDiff
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)
variable (b : Bool) (A : Finset (Slice J))

def selectLinks (v : (↑A)→G.Color) (j : Slice J) : G.Color := if h:j∈A then v ⟨j,h⟩ else 0

def lampShape (v : (↑A)→G.Color) : ℝ :=
  look b (exhibit J (fun i=>G.lieExp (selectLinks J A v i)))

theorem lampShape_hot : ContDiffAt ℝ ω (lampShape J b A) 0 := by
  let f := fun (v : (↑A)→G.Color) (i : Slice J) => turn (selectLinks J A v i)
  have h (i : Slice J) : ContDiff ℝ ω (fun (v : (↑A)→G.Color)=>selectLinks J A v i) := by
    unfold selectLinks;split <;> fun_prop
  have hot : ContDiff ℝ ω f:=contDiff_pi.mpr fun i=>turn_hot.comp (h i)
  have f₀ : f 0=0:=by funext i;simp [f,selectLinks,turn]
  have good : ContDiffAt ℝ ω ((look b ∘ sight J) ∘ f) 0 :=
    (f₀.symm ▸ sphere J b).comp 0 hot.contDiffAt
  apply good.congr_of_eventuallyEq
  have all (i : Slice J) : ∀ᶠ v : (↑A)→G.Color in 𝓝 0,
      launch (G.curvature (G.lieExp (selectLinks J A v i)))=G.lieExp (selectLinks J A v i) := by
    have ht : Tendsto (fun v : (↑A)→G.Color=>G.lieExp (selectLinks J A v i)) (𝓝 0) (𝓝 (1:G.El)) := by
      simpa [selectLinks,Function.comp_def] using (G.lieExp_cont.comp (h i).continuous).tendsto 0
    exact ht.eventually leaving
  filter_upwards [eventually_all.mpr all] with v hv
  exact congrArg (fun z=>look b (exhibit J z)) (funext fun j=>(hv j).symm)

def lampRow (n : ℕ) : Pot (Wire G (↑A)) :=
  ∑ a : Fin n → Wire G (↑A), MvPolynomial.C (YM.Tensor.coeff (lampShape J b A) n 0 (fun i=>Lumen.one (a i))) *
    ∏ i,MvPolynomial.X (a i)

theorem lampRow_eval (n : ℕ) (v : Wire G (↑A) → ℝ) :
    MvPolynomial.eval v (lampRow J b A n) = jet (lampShape J b A) n (Lumen.vector v) := by
  let D:=YM.Tensor.coeff (lampShape J b A) n 0
  simp only [lampRow,_root_.map_sum,_root_.map_mul,MvPolynomial.eval_C,_root_.map_prod,MvPolynomial.eval_X]
  change _ = D (fun _=>Lumen.vector v)
  rw [←Lumen.repr v,D.map_sum (fun (_ : Fin n) i=>v i • Lumen.one i)]
  apply sum_congr rfl;intro a _
  rw [D.map_smul_univ];exact mul_comm .. 

/-- One Taylor remainder envelope is valid for all torus sizes, forest masks and
placements of the same physical field shape. -/
theorem lampRows_remainder (n : ℕ) :
    ∃ δ C:ℝ, 0<δ ∧ 0≤C ∧ ∀ (v:Wire G (↑A)→ℝ) (g:ℝ), 0<g → g*‖Lumen.vector v‖≤δ →
      ‖lampShape J b A (g • Lumen.vector v) -
        ∑ k∈Finset.range (n+1), g^k*MvPolynomial.eval v (lampRow J b A k)‖
        ≤ C*‖Lumen.vector v‖^(n+1)*g^(n+1) := by
  obtain ⟨δ,C,pos,cap,paid⟩:=deposition (lampShape J b A) n ((lampShape_hot J b A).of_le le_top)
  refine ⟨δ,C,pos,cap,fun v g hg room=>?_⟩
  simp_rw [lampRow_eval]
  exact paid (Lumen.vector v) g hg room

end YM.Integration.FVA1Physical.Round2.Curvature
