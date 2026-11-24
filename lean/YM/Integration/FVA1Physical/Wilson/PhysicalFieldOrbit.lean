import YM.Integration.FVA1Physical.Wilson.BankOrbit
import YM.Integration.FVA1Physical.Sources.Round2.FieldMasks

/-! Volume-uniform inherited finite Wilson histories, seeded by the actual
finite menu of physical field stencils and on one selected Yang–Mills run.
Every level uses that scene's own action, conditional vacuum and coupling
reset. Additional compatible purchases may be made on the identical run. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {μ:Type} [Fintype μ] {κ:μ→Type} [∀ a, Fintype (κ a)]

theorem physical_field_orbits (I:∀ a,κ a→Lamp G) {goal:Qlocal.Schedule.Goal G}
    (extra:Qlocal.Schedule.Obtainable goal) (simple:G.Simple) (cost:ℝ) (positive:0<cost) :
    ∃ (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex),
       R.family.path.levels.clock.kernel.penalty=cost ∧ goal R.metals R.rolls R.alloy R.kit ∧ R.metals.O=chart G ∧
       ∀ (p d s L:ℕ), 6 ≤ s → ∀ η:ℝ,0<η →
       ∀ᶠ k:ℕ in atTop,∀ N n,k ≤ N → ∃ S:Scene R.family.path.levels n (p+1+p),
         Realized R.alloy.B.kin N n k (p+1+p) (Lis.sun G u) S ∧
         ∀ j,k ≤ j → j+d<N → ∀ (fs:∀ i, Forest (R.family.path.levels.clock.op i n).ratio)
           (vs:∀ i,(R.family.path.levels.clock.op i n).Choices) (b:∀ i,Site (R.family.path.levels.S.side i n)),
           (∀ i,j ≤ i → i<j+d → (R.family.path.levels.clock.op i n).ratio.embed (b i)=b (i+1)) →
           ∀ (a:μ) (part:Bool) (o:∀ i,κ a→Site (R.family.path.levels.S.side (i+1) n)),
           let θ:=R.family.path.levels.clock.hatBeta
           let A (i : ℕ) :=sceneIssue (N:=N) (RunFormalChain.fromRun R) S (fs i) (vs i)
           (∀ t:Slice (I a),separation ((A (j+d)).S.ratio.embed (b (j+d))) (legs (I a) (o (j+d)) t).1 ≤ L*closeN (θ (j+d+1))) →
           let T (i : ℕ) :=emittedRows (A i) R.metals.O (jointFieldBank (I a) (A i) (o i) part) p
           BankPaid (b j) (θ j) s p (orbitDegree p (emittedDegree p) d) η
              (bankOrbit R N S fs vs p (emittedDegree p) T d j) := by
  haveI:=simple.nontrivial_color
  have dim:0<G.lieDim:=by rw [Gauge.lieDim,←G.colorIso.finrank_eq];exact Module.finrank_pos
  letI : Nonempty G.ColorIndex := ⟨⟨0,dim⟩⟩
  obtain ⟨V,cl⟩:=MSbar.Heath.vocals G
  let offer:=extra.also (Round2.Curvature.finiteInvoice (fun u:G.ColorIndex=>iteratedBankInvoice u V cl simple)
    (fun u=>bankInvoice_obtainable u V cl simple))
  obtain ⟨R,u,pen,⟨done,accounts⟩,frame,seeds⟩:=all_orders_coarse_fields I offer simple cost positive
  refine ⟨R,u,pen,done,frame,?_⟩
  intro p d s L hs η hη
  let m:=emittedDegree p
  let r:=p+1+p
  obtain ⟨δ,δpos,buy⟩:=all_fixed_bank_orbits simple R u V cl frame (accounts u) r p m s d
    (by dsimp only [r];omega) (by dsimp only [m,emittedDegree];omega) hs hη
  filter_upwards [buy,seeds p s m L hs 0 δ le_rfl δpos] with k path seed
  intro N n kn
  obtain ⟨S,scene,rows⟩:=seed N n kn
  refine ⟨S,scene,?_⟩
  intro j kj jN fs vs b consistent a part o θ A near T
  apply path N n S scene j kj jN fs vs b T consistent
  intro i hi
  have tr:=(scene.budget (j+d+1) jN (by omega)).1
  have raw:=(rows (j+d) (by omega) jN (fs (j+d)) (vs (j+d)) a part (b (j+d)) 0 (by simp)
    (o (j+d)) near i hi).2
  refine ⟨emitted_field_degree (A (j+d)) R.metals.O (I a) (o (j+d)) part p tr.bond tr.plane hi,?_⟩
  dsimp only [T,A,θ]
  simp only [smul_zero] at raw
  exact raw

end YM.Integration.FVA1Physical.Wilson
