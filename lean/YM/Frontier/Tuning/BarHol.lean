import YM.Frontier.Tuning.MeristemC
import YM.Frontier.Tuning.JetHol
import YM.Frontier.Tuning.HolColor
import YM.Frontier.Tuning.RecoilIdentity
import YM.Frontier.Tuning.WingC
import YM.Frontier.Tuning.ZestPalette
import YM.Frontier.Tuning.CarryC

/-! Actual integration bounds before period by combining postperiod neighborhood domination with pointwise angular estimates (later). No gluing of masks varying with the draw. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Frontier.Tuning.BarHol
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Blaze Art Silica Poll Pond Eider Flux Held GlassLog Zest TwoMotion RecoilIdentity Shield DensityTilt PhysicalNext.Repeat.Alabaster
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]{x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {η Y r' Q' W : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Q:ConnectedActivityE6.Target G P} {R R': Rep G f}
variable (hP : Port P L η r' Q' Y X)
variable (ho : Intake P T X.x R) (ht:Facing R R')(hr:Intake P T X.x R')
variable (J : Finset (Bond f)) {K K' : ℝ} (hK:Canary G K K')(z':Molecule S)
variable {μ S0 C'':ℝ}{o:Target.Order G W}(H0: Cash W S0 μ L Q o C'' T R)
local notation "pbar" => edgesM S (H0.unionP z') (radiusB X.x)
variable (hX: X.width=o.K) (hS:X.x = S0) (he : 8*o.a*X.t ≤ K/2) (U : Set ℂ) (τ:ℂ→ℂ)(e'f h:ℂ→Payload G f) (hU:IsOpen U)(hτ:DifferentiableOn ℂ τ U) {bM:ℝ}
   (hb : ∀ i∈U,0<(τ i).re ∧ fans R R' bM (e'f i) (h i))(_he : ∀ n y,DifferentiableOn ℂ (fun z=>e'f z n y) U)(hh : ∀ n y,DifferentiableOn ℂ (fun z=>h z n y) U)
include H ht hr hP hK H0 hX hS he hU hτ hb _he hh
lemma local_bounds (c:ℂ)(hc:c∈U):
    let a:=o.a; let M:=(F.order G).prod X.dice
    let g i y s:= rotor pbar K (C y) z' (e'f i) (h i) R (X.wrapY s.1) Q.table a W Q.halo (τ i) s.2
    let f y i := barC pbar R (e'f i) (h i) (vary X (C y)) Q.table a W Q.halo z' (τ i)
    ∃ B>0, ∃ T'∈𝓝 x,∃ S'∈𝓝 c,∃ D, IsOpen S' ∧ IsOpen T' ∧ Integrable D M ∧ (∀ y∈T', DifferentiableOn ℂ (f y) S') ∧
    (∀ y∈T', ∀ i∈S', f y i=∫ z,g i y z ∂M) ∧ ∀ i∈S',∀ y∈T',Meristem (g i) y M j ∧ ∫ z,D z ∂M ≤ B ∧ ∀ z, Brush j (D z) 1 (g i · z) y:=by
    intro a M g f
    have hg : ContinuousAt τ c:= hτ.continuousOn.continuousAt (hU.mem_nhds hc)
    have hV0:τ c∈Complex.slitPlane:= Or.inl (hb c hc).1
    have hl := (Complex.differentiableAt_log hV0).continuousAt.comp hg
    have hm := (HolColor.tint (O:=Q.table) (hτ.differentiableAt (hU.mem_nhds hc)) hV0).continuousAt
    let m := (τ c).re/2; let C' := 1+‖τ c‖+‖Complex.log (τ c)‖+‖ComplexVertex.logMass Q.table (τ c)‖
    have hχ : ∀ᶠ i in 𝓝 c, i∈U ∧ ‖τ i‖ ≤ C' ∧ m≤ (τ i).re ∧ ‖Complex.log (τ i)‖ ≤ C' ∧ ‖ComplexVertex.logMass Q.table (τ i)‖ ≤ C' := by
      filter_upwards [hU.mem_nhds hc,hg.norm.eventually (ge_mem_nhds (show ‖τ c‖<C' from by unfold C'; linarith only [norm_nonneg (Complex.log (τ c)),norm_nonneg (ComplexVertex.logMass Q.table (τ c))])),(Complex.continuous_re.continuousAt.comp hg).eventually (le_mem_nhds (half_lt_self (hb c hc).1)),hl.norm.eventually (ge_mem_nhds (show ‖Complex.log (τ c)‖<C' from by unfold C'; linarith only [norm_nonneg (τ c),norm_nonneg (ComplexVertex.logMass Q.table (τ c))])),hm.norm.eventually (ge_mem_nhds (show ‖ComplexVertex.logMass Q.table (τ c)‖ < C' from by unfold C';  linarith only [norm_nonneg (Complex.log (τ c)),norm_nonneg (τ c)]))] with i hi h h' h1 h2 using ⟨hi,h,h',h1,h2⟩
    obtain ⟨S',hS',hSc,hS0⟩:=_root_.mem_nhds_iff.mp hχ
    obtain ⟨D,hD,hp⟩:= MeristemC.price_region H hP ht hr pbar hK z' H0 hX hS he S' τ e'f h (bM:=bM) (half_pos (hb c hc).1) (cM:=C') (by unfold C'; positivity)
      (fun i hi=> (hS' hi).2) (fun i hi=>(hb i (hS' hi).1).2)
    obtain ⟨v,hv⟩:= H.sails
    obtain ⟨T',hT',hTx,hT0⟩:= _root_.mem_nhds_iff.mp (hp.and (nearby X hK H.lifts hv))
    have intg y (hy:y∈T') i (hi:i∈S') : Integrable (g i y) M := hD.mono' (((hT' hy).1 _ hi).1.aestronglyMeasurable) (ae_of_all _ fun t=>(((hT' hy).1 _ hi).2 t).bound)
    have hΛ: ShellAccess S G X.x W X.width o.γ := hS.symm ▸ hX.symm ▸ H0.laws.data.access
    have eq (y:E)(hy:y∈T')(i:ℂ)(hi:i∈S') : f y i= ∫ z,g i y z ∂M := by
      rw [integral_prod _ (intg y hy i hi)]; dsimp only [f]
      obtain ⟨r,s,p,q,_,_,_,_,hx,hV⟩:= (hb i (hS' hi).1).2
      have hx' i y:e'f _ i y=r*R.activities.E i y+s*R'.activities.E i y:= congr_fun (congr_fun hx i) y
      have hV' i y:h _ i y=p*R.activities.K i y+q*R'.activities.K i y:=congr_fun (congr_fun hV i) y
      exact RecoilIdentity.transition hx' hV' ht (hS.symm ▸ H0.laws.intake) pbar K (C y) z' hK (hT' hy).2 H.winter (by change edgesM S (ground R T Q.halo (radiusB S0) z') _=_; rw [← hS]) Q.buys hr hΛ Q.table_exists hP.sails.room
    refine ⟨|∫ z,D z ∂M|+1,by positivity,T',hTx.mem_nhds hT0,S',hSc.mem_nhds hS0,D,hSc,hTx,hD,fun y hy=> ?_, fun y hy i hi=>eq y hy i hi, fun i hi y hy=>⟨?_,?_⟩⟩ -- replace
    · have ht' : DifferentiableOn ℂ (fun z=>∫ s,g z y s ∂M) S':=DominatedHol.analytic_loc hSc (fun i hi=> (intg y hy i hi).1) (fun v i hi=> HolColor.spin _ R (hτ.differentiableAt (hU.mem_nhds (hS' hi).1)) (Or.inl (hb i (hS' hi).1).1) _ K (C y) z' (fun j y=>(_he j y).differentiableAt (hU.mem_nhds (hS' hi).1)) (fun j y=>(hh j y).differentiableAt (hU.mem_nhds (hS' hi).1))) (fun i hi=> ⟨S',hSc.mem_nhds hi,D,hD,fun i hi v=> (((hT' hy).1 i hi).2 v).bound⟩)
      exact ht'.congr (fun z hz=>(eq y hy z hz))
    · -- points ℝ value too restrictive; replicate
      have hv y (hy:y∈T'):AEStronglyMeasurable (g i y) M:=(intg y hy i hi).1
      have hsmooth (y:E)(hy:y∈T')(v) : Brush j (D v) 1 (g i · v) y:=((hT' hy).1 i hi).2 v
      refine ⟨T',hTx.mem_nhds hy,ae_of_all _ (fun v s hs=>(hsmooth s hs v).smooth),fun k hk=> ⟨D,hD,fun s hs=> ?_,ae_of_all _ fun z y hy=>?_⟩⟩
      · exact (Meristem.legs hTx (fun i t ht=>(hsmooth t ht i).smooth) (fun t ht=> ((hT' ht).1 i hi).1.stronglyMeasurable) hk hs).aestronglyMeasurable
      simpa only [one_pow,mul_one] using (hsmooth y hy z).order k hk
    · exact ⟨(le_abs_self _).trans (le_add_of_nonneg_right zero_le_one),((hT' hy).1 i hi).2⟩
lemma jets : let f y i := barC pbar R (e'f i) (h i) (vary X (C y)) Q.table o.a W Q.halo z' (τ i)
    ∀ k≤j,∀ m:Fin k→E,DifferentiableOn ℂ (fun i=> iteratedFDeriv ℝ k (f · i) x m) U:=by
    intro f k hk m i hi
    obtain ⟨B,hB,T',hx,S',hs,D,hG,hT,hD,hP',hR',hQ'⟩:= local_bounds H hP ht hr hK z' H0 hX hS he U τ _ _ hU hτ hb _he hh i hi -- infer J ?
    have brush y (hy:y ∈ T') i (hi:i∈S') : Brush j B 1 (f · i) y :=by
      apply (((hQ' i hi y hy).1.buds D hD zero_le_one (hQ' i hi y hy).2.1 (ae_of_all _ (hQ' i hi y hy).2.2))).shimmy ((show ∀ᶠ z in 𝓝 y,z∈T' from hT.mem_nhds hy).mono fun y hy=>hR' y hy i hi)
    exact (JetHol.derivative_exchange hT hG (fun y hy=> ⟨hP' y hy,brush y hy⟩) k hk x (Filter.Eventually.self_of_nhds hx) m).differentiableAt hs |>.differentiableWithinAt
end YM.Frontier.Tuning.BarHol
