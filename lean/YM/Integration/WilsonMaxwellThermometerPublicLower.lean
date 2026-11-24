import YM.Integration.WilsonMaxwellThermometerPublicFaceLimits
import YM.Integration.WilsonMaxwellThermometerNominatedSchurFree

/-! The genuine smeared lower component of the public Schur correction
tends to zero along the physical regulator order, for every filed
grade-four diagnostic. This allows a rate on the calibration bag to pay
the public restoration without a separate rate on these triangles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicLower
open Filter Function Set Finset Metric MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato
open RG17 XSpace XSpace.Structure1 XSpace.Tornado XSpace.Normalize OPE OPE.Orbits Climb Table Spec Extraction Trace Trace.Pilot Next.UVStress PhysMS
open Maxwell Maxwell.Free WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonMaxwellThermometerPublicFaces WilsonMaxwellThermometerPublicFaceLimits
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (K:Rose.Pick V) (A:ℝ→Group R.family 6)
local notation "D" => ((fun _:Fin 3=>(4:ℕ)):Caps 3)
local notation "a" => (by decide : 4≤6)

def tags (e:RG17.Free R.family 4):Tags G 6 3:=
  Graph3.trip (up a (fields R.family.labels 4 e)) (up a (WilsonPositionThermometerGradedSource.lower G))
    (up a (WilsonPositionThermometerGradedSource.lower G))

theorem free (e:RG17.Free R.family 4) (s:Badge₃) (x:Points 3):
    ground R e x s=WilsonMaxwellThermometerFaces.faces x (tags R e) s:=by
  let v:=slots R (leg R e) s
  let input (i:Fin 3):(Bel R.family.book).Tag:=⟨4,v i⟩
  change (Bel R.family.book).useAt (Bel R.family.book) x input=_
  rw [Maxwell.Free.display]
  have same:Maxwell.Free.supply R.family.labels ∘ input=fun i=>(Rose.missing (tags R e) s i).val:=by
    funext i
    change address R.family.labels _ (v i)=_
    by_cases h:i∈s
    · simp only [address_eval,v,slots,if_pos h,Rose.missing]
      fin_cases i <;> simp [WilsonMaxwellThermometerPublicFaceLimits.leg,tags,Graph3.trip]
    · simp only [v,slots,if_neg h,Rose.missing,unit_address]
      rfl
  rw [same]
  rfl

theorem zero (simple:G.Simple) (e:RG17.Free R.family 4):
    (Rose.test K).applyTo (fun x=>WilsonPositionThermometerConnected.value (ground R e x))=0:=by
  have fac (x:Points 3):WilsonPositionThermometerConnected.value (ground R e x)=
    WilsonMaxwellThermometerFaces.connected x (tags R e):=by
    rw [funext (fun s=>free R e s x)]
    simp only [WilsonPositionThermometerConnected.value,WilsonMaxwellThermometerFaces.connected,Rose.b3,
      two_smul,map_add,map_sub,map_mul,PowerSeries.constantCoeff_C]
    ring
  simp only [fac]
  exact WilsonMaxwellThermometerOriginal.moved simple K (up a (fields R.family.labels 4 e)) LinearMap.id (fun _ _=>rfl)

variable {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
  (simple:G.Simple) (hl:(Y:Filter _)≤f.fuse) (book:Book (f:=f) (l:=Y) (H:=H) A J)
local notation "L" => trail.curry (Y:Filter (ℕ×ℕ))

include simple hl book in
theorem original (lead:Leading F J) (e:RG17.Free R.family 4):
    Tendsto (fun w:ℝ×(ℕ×ℕ)=>WilsonMaxwellThermometerPublicPocket.measured R F J V K A w.1 w.2 e) L (𝓝 0):=by
  let Φ:=Rose.test K
  let E:=tsupport Φ
  let G₀:=ground R e
  let field (w:ℝ×(ℕ×ℕ)) (x:Points 3):=faces R F J V A w.1 e w.2 (WilsonSeparatedOriginalThermometerCells.positions (R:=R) w.1 w.2 x)
  let score:=WilsonPositionThermometerConnected.value
  have regular:ContinuousOn G₀ (conf 3):=by
    apply continuousOn_pi.mpr
    intro s x hx
    exact (WickGoal_tied (C:=R.family) (d:=D) (slots R (leg R e) s) hx).continuousAt.continuousWithinAt
  have uk:IsCompact (G₀ '' E):=Φ.hasCompactSupport.image_of_continuousOn (regular.mono Φ.tsupport_subset)
  let W:=cthickening 1 (G₀ '' E)
  have wc:IsCompact W:=uk.cthickening
  have continuum:Φ.applyTo (fun x=>score (G₀ x))=0:=zero R V K simple e
  have lit:∀ᶠw:ℝ×(ℕ×ℕ) in L,WilsonMaxwellThermometerPublicPocket.measured R F J V K A w.1 w.2 e=
      Φ.applyTo (fun x=>score (field w x)):=by
    apply eventually_curry_iff.mpr
    filter_upwards [book 0] with r cert
    exact (literal R F J V K A r e cert.2.1).filter_mono hl
  have limit (ε:ℝ) (hε:0<ε):∀ᶠw:ℝ×(ℕ×ℕ) in L,∀x∈E,‖score (field w x)-score (G₀ x)‖<ε:=by
    obtain ⟨δ,hd,close⟩:=Metric.uniformContinuousOn_iff.mp
      (wc.uniformContinuousOn_of_continuous WilsonPositionThermometerConnected.continuous_value.continuousOn) ε hε
    have hδ:0 < min 1 δ:=lt_min one_pos hd
    have paid:=eventually_all.mpr (fun s:Badge₃=>WilsonMaxwellThermometerPublicFaceLimits.original R F J V A simple hl book lead e s
      Φ.hasCompactSupport Φ.tsupport_subset _ hδ)
    filter_upwards [paid] with w bank x hx
    have near:dist (field w x) (G₀ x) < min 1 δ:= (dist_pi_lt_iff hδ).mpr fun s=>by
      simpa only [dist_eq_norm] using bank s x hx
    have inside:G₀ x∈G₀ '' E:=⟨x,hx,rfl⟩
    simpa only [score,dist_eq_norm] using close _ (mem_cthickening_of_dist_le _ _ 1 _ inside (near.le.trans (min_le_left ..))) _
      (self_subset_cthickening (G₀ '' E) inside) (near.trans_le (min_le_right ..))
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let M:=∫x:Points 3,‖Φ x‖
  have hm:0≤M:=integral_nonneg fun _=>norm_nonneg _
  let t:ℝ:=ε/(M+1)
  have ht:0<t:=div_pos he (by linarith)
  have fee:M*t<ε:=calc
    _ < (M+1)*t:=mul_lt_mul_of_pos_right (lt_add_one _) ht
    _ = ε:=by dsimp only [t];field_simp
  have gi:Integrable (fun x:Points 3=>Φ x):=Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
  have oi:Integrable (fun x:Points 3=>Φ x*score (G₀ x)):=
    Φ.smearing (WilsonPositionThermometerConnected.continuous_value.comp_continuousOn regular)
  filter_upwards [limit t ht,lit] with w bound source
  have meas:Measurable (fun x=>score (field w x)):=(measurable_of_finite (fun u=>score (faces R F J V A w.1 e w.2 u))).comp
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) w.1 w.2)
  have point (x:Points 3):‖Φ x*score (field w x)-Φ x*score (G₀ x)‖≤‖Φ x‖*t:=by
    by_cases hz:Φ x=0
    · simp [hz]
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (bound x (subset_closure hz)).le (norm_nonneg _)
  have di:Integrable (fun x=>Φ x*score (field w x)-Φ x*score (G₀ x)):=(gi.norm.mul_const t).mono'
    ((Φ.continuous.measurable.mul meas).aestronglyMeasurable.sub oi.aestronglyMeasurable) (Eventually.of_forall point)
  have vi:Integrable (fun x=>Φ x*score (field w x)):=(di.add oi).congr (Eventually.of_forall fun _=>sub_add_cancel _ _)
  rw [source,←continuum,dist_eq_norm]
  change ‖(∫x,Φ x*score (field w x))-(∫x,Φ x*score (G₀ x))‖<ε
  rw [←integral_sub vi oi]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point))
  rw [integral_mul_const]
  exact fee
end YM.Integration.WilsonMaxwellThermometerPublicLower
