import YM.Integration.WilsonSeparatedPhysicalOrder

/-! Direct continuum passage on the unselected Wilson law for arbitrary
distinct inner points of the grid and arbitrary distinct exterior
points. The evolving counterterm is the actual cluster of the full
moving product, not a prescribed independent field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedFusedReadout
open Function Filter MeasureTheory Lattice Wilson RG Cells Extraction OPE OPE.Orbits OPE.Cards OPE.Log
open StressFlux.Matching Frontier6.Road Trace.Pilot
open WilsonWholeLimit FilteredIntrinsicGramReadout FilteredWilsonProduct FilteredProductLimit
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {de : E → ℕ} {D : ℕ}

private theorem zero_site (w : ℕ × ℕ) : ceilSite C w.1 w.2 (0:E4) = 0 := by
  change Lattice.wrap _ (fun _ => ⌈(0:ℝ)/C.S.a w.1⌉) = 0
  simp only [zero_div,Int.ceil_zero]
  exact (Lattice.wrap _).map_zero

private def meter (T : Table C.book) (y : E → E4) (w : Labels S de) :
    C.label D →ₗ[ℂ] ℂ :=
  T.injectFront (names w ∘ runNames E) (Points.cons 0 (points (y ∘ runNames E))) D

private theorem finiteMeter (y : E → E4) (w : Labels S de) (s : ℕ×ℕ) (z : C.label D) :
    meter (rounded C s.1 s.2) y w z = Wilson.moment (C.beta s.1 s.2)
      (C.O s.1 s.2 z 0 * product y w s.1 s.2) := by
  let tok : Fin (Fintype.card E+1) → C.book.Token := Fin.cons (⟨D,z⟩:C.book.Token) (names w ∘ runNames E)
  let p := Points.cons 0 (points (y ∘ runNames E))
  change Wilson.moment (C.beta s.1 s.2) (fun V=>∏ i,C.seen (tok i) (ceilSite C s.1 s.2 (p i)) V)=_
  apply congrArg (Wilson.moment (C.beta s.1 s.2))
  funext V
  rw [Fin.prod_univ_succ]
  simp only [tok,p,Points.cons,points_apply,Fin.cons_zero,Fin.cons_succ,zero_site,comp_apply,Pi.mul_apply]
  exact congrArg (fun q:ℂ=>C.O s.1 s.2 z 0 V*q)
    ((runNames E).prod_comp (fun i=>C.seen (names w i) (ceilSite C s.1 s.2 (y i)) V))

private theorem counterterm (F : Spec.Final C f S) (hs : Services C f S)
    (y : E → E4) (w : Labels S de) (outside : Injective (beside (sole (0:E4)) y))
    {l : Filter (ℕ×ℕ)} (sub : l ≤ f.fuse) {raw : ℕ×ℕ → C.label D} {z : C.label D}
    (hz : Tendsto raw l (𝓝 z)) :
    Tendsto (fun s:ℕ×ℕ=>Wilson.moment (C.beta s.1 s.2)
      (C.O s.1 s.2 (raw s) 0 * product y w s.1 s.2)) l
        (𝓝 (upon S D 0 y w (S.project D z))) := by
  let coord := Points.cons 0 (points (y ∘ runNames E))
  let N := meter S y w (D:=D)
  let M (s:ℕ×ℕ) := meter (rounded C s.1 s.2) y w (D:=D)
  have canonical (a:C.label D) : N a = upon S D 0 y w (S.project D a) := by
    rw [upon_observe _ w F.room.kernel (fun _ => le_rfl) outside,
      projectedOne S _ D a F.room.kernel.laws.toSymmetric (fun _=>le_rfl) outside]
    exact (head_observe (e:=runNames E) S (names w) _ F.room.kernel.laws.toSymmetric outside).symm
  have fixed (a:C.label D) : Tendsto (fun s=>M s a) l (𝓝 (N a)) :=
    (rounded_tendsto_separated F hs (Fin.cons (⟨D,a⟩:C.book.Token) (names w ∘ runNames E))
      coord (consIn (e:=runNames E) 0 y |>.2 outside)).mono_left sub
  let b := Module.finBasis ℂ (C.label D)
  have expansion (h:C.label D →ₗ[ℂ] ℂ) (a:C.label D) : h a = ∑ i,b.repr a i*h (b i) := by
    conv_lhs => rw [←b.sum_repr a]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
  rw [←canonical,expansion N z]
  apply (tendsto_finsetSum Finset.univ (fun k _=>
    ((b.coord k).continuous_of_finiteDimensional.continuousAt.tendsto.comp hz).mul (fixed (b k)))).congr'
  exact Eventually.of_forall fun s=>(expansion (M s) (raw s)).symm.trans (finiteMeter y w s (raw s))

private theorem fine_product {e : I → ℕ} (j : ℕ) (x : I → Cover) (v : Labels S e) (s : ℕ × ℕ) (hj : j ≤ s.1) :
    leaves C j e x (fun i=>S.representative _ (v i)) s.1 s.2 = product (C.S.gridPoint j ∘ x) v s.1 s.2 := by
  have rows (a:Cover) : ceilSite C s.1 s.2 (C.S.gridPoint j a) = location C.S j s.1 s.2 a := by
    simpa only [zero_add,zero_site] using WilsonExteriorGeometry.ceilSite_add_grid (C:=C) (p:=s.2) hj (0:E4) a
  funext V
  simp only [leaves,Finset.prod_apply,product,comp_apply,rows]
  rfl

private theorem jointProduct (F : Spec.Final C f S) (hs : Services C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i:I) → (Climb.Bel C.book).Field (d i))
    (r : ℝ) (j : ℕ) (x : I → Cover) (y : E → E4) (w : Labels S de)
    (sep : Injective (beside (C.S.gridPoint j ∘ x) y)) :
    Tendsto (fun s:ℕ×ℕ=>Wilson.moment (C.beta s.1 s.2)
      (field F Q J v r j x s * product y w s.1 s.2)) f.fuse
        (𝓝 (whole S (C.S.gridPoint j ∘ x) (PhysMS.Frame.born J r v) y w)) := by
  let p := C.S.gridPoint j ∘ x
  rw [continuum F Q J v r p y w sep]
  apply (tendsto_finsetSum Finset.univ (fun g _=>
    whole_tendsto_separated F hs p (sector F Q J v r g) y w sep)).congr'
  filter_upwards [(Cards.largeMesh f).eventually_ge_atTop j] with s live
  let term (g:Grades d) := product (beside p y) (stages (sector F Q J v r g) w) s.1 s.2
  have same (g:Grades d) : term g =
      leaves C j (levels g) x (component F Q J v g r) s.1 s.2 * product y w s.1 s.2 := by
    change _= leaves C j (levels g) x (fun i=>S.representative _ (sector F Q J v r g i)) s.1 s.2 * _
    rw [fine_product j x (sector F Q J v r g) s live]
    exact funext (product_split p (sector F Q J v r g) y w s.1 s.2)
  have add : field F Q J v r j x s * product y w s.1 s.2 = ∑ g,term g := by
    rw [field_expansion,Finset.sum_mul]
    exact Finset.sum_congr rfl fun g _=>(same g).symm
  change ∑ g,Wilson.moment (C.beta s.1 s.2) (term g) = _
  rw [add]
  unfold Wilson.moment
  simp only [Finset.sum_apply]
  exact (integral_finsetSum _ (fun g _=>product_integrable _ _ s.1 s.2)).symm

/-- Regulator convergence of the signed whole product times its actual
exterior, including an arbitrarily varying intrinsic terminal label on
the same subfilter. No coordinatewise genericity is required. -/
theorem original (F : Spec.Final C f S) (hs : Services C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i:I) → (Climb.Bel C.book).Field (d i)) (r : ℝ)
    (b j : ℕ) (x : I → Cover) (y : E → E4) (w : Labels S de)
    (sep : Injective (beside (C.S.gridPoint j ∘ x) y)) (outside : Injective (beside (sole (0:E4)) y))
    {l : Filter (ℕ×ℕ)} (sub : l ≤ f.fuse) {z : C.label D}
    (hz : Tendsto (fun s=>IntrinsicProductCompactness.value (D:=D) F.room.cutoff b s (field F Q J v r j x s)) l (𝓝 z)) :
    Tendsto (fun s:ℕ×ℕ=>Wilson.moment (C.beta s.1 s.2)
      (WilsonSeparatedPhysicalCopies.gap (D:=D) F Q J v r b j x s * product y w s.1 s.2)) l
      (𝓝 (whole S (C.S.gridPoint j ∘ x) (PhysMS.Frame.born J r v) y w - upon S D 0 y w (S.project D z))) := by
  apply (((jointProduct F hs Q J v r j x y w sep).mono_left sub).sub (counterterm F hs y w outside sub hz)).congr'
  filter_upwards [(Cards.largeMesh f).eventually_ge_atTop j |>.filter_mono sub] with s live
  let ext := product y w s.1 s.2
  let inner := field F Q J v r j x s
  let label := IntrinsicProductCompactness.value (D:=D) F.room.cutoff b s inner
  have cfield : Continuous inner := by
    change Continuous (field F Q J v r j x s)
    rw [field_expansion]
    rw [show (∑ g,leaves C j (levels g) x (component F Q J v g r) s.1 s.2) =
      (fun V:Config G (C.side s.1 s.2)=>∑ g,leaves C j (levels g) x (component F Q J v g r) s.1 s.2 V)
      from funext fun V=>Finset.sum_apply ..]
    apply continuous_finsetSum _ (fun g _=>?_)
    change Continuous (leaves C j (levels g) x (fun i=>S.representative _ (sector F Q J v r g i)) s.1 s.2)
    rw [fine_product j x (sector F Q J v r g) s live]
    exact product_continuous .. 
  change Wilson.moment (C.beta s.1 s.2) (inner*ext) - Wilson.moment _ (C.O s.1 s.2 label 0*ext) =
    Wilson.moment _ ((inner-C.O s.1 s.2 label 0)*ext)
  rw [sub_mul]
  exact (integral_sub (continuous_integrable _ (cfield.mul (product_continuous ..)))
    (continuous_integrable _ ((C.continuousO ..).mul (product_continuous ..)))).symm

end YM.Integration.WilsonSeparatedFusedReadout
