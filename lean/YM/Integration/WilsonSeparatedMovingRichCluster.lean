import YM.Integration.WilsonSeparatedMovingRichCharge
import YM.Integration.WilsonSeparatedMovingRichGeometry
import YM.Integration.WilsonSeparatedRichExteriorBank

/-! At the genuinely moving length τ=r^a, integrate the full joint
physical-separation estimate on the independently registered rich test.
The two sides use one true Wilson family and one cutoff cluster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingRichCluster
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Filter Set MeasureTheory Lattice Extraction Table Spec Climb OPE OPE.Orbits RG17 SharpGram PhysMS
open Trace.Pilot Frontier6.Road SharedIntrinsicWilsonGrid IntrinsicWilsonTensor ContinuumIntrinsicWilsonProduct WilsonSeparatedMovingRichGeometry
open Next.UVStress OPE.Cards
open scoped Classical BigOperators Topology
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {V:Table C.book}
variable {I:Type} [Fintype I] {d:I→ℕ} {D:ℕ}

/-- The same registered physical exterior integral, available on every native
family, before specializing to a particular funded Run. -/
def observed (B:Deck G) (J : ℝ→tower V) (φ : Test 2) {τ:ℝ} (tp:0<τ) (D:ℕ)
    (near:I→E4) (ins:Labels V d) : Glyph B D → ℂ := fun b=>
  let X := WilsonMacroscopicRichRegister.exterior B J φ tp b
  ∫ z,X.test z * whole V near ins (X.offset z) X.labels

private lemma zoom (φ:Test 2) {τ:ℝ} (tp:0<τ) (K:(Fin 1→E4)→ℂ) :
    (Next.UVStress.dilate tp φ).applyTo (fun z:Points 2=>K (fun i=>z i.succ-z 0)) =
      ∫ z,φ z*K (far τ z) := by
  rw [Next.UVStress.zoom_integral]
  apply integral_congr_ae
  filter_upwards with z
  apply congrArg (φ z* ·)
  apply congrArg K
  funext i
  change τ • z i.succ-τ • z 0=τ • (z i.succ-z 0)
  rw [smul_sub]

private lemma integrable (F : Final C f V) (φ:Test 2) (τ:ℝ) (near:I→E4) (v:Labels V d)
    (w:Labels V (fun _:Fin 1=>D)) (clean:∀ z∈tsupport φ,Injective (beside near (far τ z))) :
    Integrable (fun z=>φ z*whole V near v (far τ z) w) := by
  refine RG17.localized φ _ (fun z hz=>?_)
  let loc (t:Points 2) : Orbits.Loc I (Fin 1) := (near,(0:E4),far τ t)
  have hf : Continuous (far τ) := by unfold far;apply continuous_pi;intro i;fun_prop
  have hc : Continuous loc := continuous_const.prodMk (continuous_const.prodMk hf)
  exact (Orbits.whole_cont_at v w V F.room.kernel (x:=loc z) (clean z hz)).comp (f:=loc) hc.continuousAt

private lemma single {τ η:ℝ} (ep:0<η) (z:Points 2) (safe:ClearOf 0 (far τ z) η) :
    Injective (beside (sole (0:E4)) (far τ z)) := by
  apply beside_distinct.mpr
  refine ⟨fun _ _ _=>Subsingleton.elim _ _,fun _ _ _=>Subsingleton.elim _ _,?_⟩
  intro _ i eq
  have h:=safe.openSpace i
  change (0:E4)=far τ z i at eq
  change η≤‖(0:E4)-far τ z i‖ at h
  rw [←eq,sub_self,norm_zero] at h
  exact ep.not_ge h

/-- Exact finite basis expansion of the *integrated* physical full product.
The support clearance purchases integrability of every finite basis column. -/
theorem expanded (F : Final C f V) (B:Deck G) (J : ℝ→tower V) (φ:Test 2) {τ:ℝ} (tp:0<τ)
    (D:ℕ) (near:I→E4) (clean:∀ z∈tsupport φ,Injective (beside near (far τ z)))
    (r:ℝ) (v:(i:I)→Input C (d i)) (col:Glyph B D) :
    observed B J φ tp D near (Frame.born J r v) col =
      ∑ u:Code (fun i=>Input C (d i)),coords _ u v * observed B J φ tp D near (Frame.born J r (combination _ u)) col := by
  let Y (i:I):=Input C (d i)
  let w:=Frame.born J τ (d:=fun _:Fin 1=>D) (fun _=>WilsonMacroscopicRichFree.basis C B D col)
  let A (v:(i:I)→Y i) (u:Points 2):=whole V near (Frame.born J r v) (far τ u) w
  have seen (v:(i:I)→Y i):observed B J φ tp D near (Frame.born J r v) col=∫ u,φ u*A v u :=
    zoom φ tp (fun y=>whole V near (Frame.born J r v) y w)
  have hi (v:(i:I)→Y i):Integrable (fun u=>φ u*A v u) := integrable F φ τ near (Frame.born J r v) w clean
  let M (u:Points 2):MultilinearMap ℂ Y ℂ :=
    (sectionLabels (d:=Sum.elim d (fun _:Fin 1=>D)) w (Orbits.moment V (beside near (far τ u)))).compLinearMap
      (fun i=>(J r (d i)).toLinearMap)
  have exactValue (u:Points 2) (v:(i:I)→Y i) : M u v = A v u := by
    change sectionLabels (d:=Sum.elim d (fun _:Fin 1=>D)) w (Orbits.moment V (beside near (far τ u))) (Frame.born J r v)=_
    rw [sectionLabels_apply]
    rfl
  calc
    _=∫ z,φ z*A v z := seen v
    _=∫ z,∑ u:Code Y,coords Y u v*(φ z*A (combination Y u) z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [←exactValue,basis_tuple Y v (M z),Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _=>by rw [exactValue];ring
    _=∑ u:Code Y,coords Y u v*(∫ z,φ z*A (combination Y u) z) := by
      rw [integral_finsetSum _ (fun u _=>(hi (combination Y u)).const_mul _)]
      simp only [integral_const_mul]
    _=_ := Finset.sum_congr rfl fun u _=>by rw [seen]

theorem original (F : Final C f V) (fac : Facilities C f V) (anchor:I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) (J : ℝ→tower V) (lead:Leading F J) (B:Deck G) (φ:Test 2)
    (v:(i:I)→(Bel C.book).Field (d i)) {g:ℝ→ℝ} (hg:Coupling G g) (hG:G.Simple) {a b:ℝ}
    (ap:0<a) (ab:a<b) (edge:3*b<P.h) (reserve:((D:ℝ)+1)*(4*b)<1/32) (k:ℕ) (ε:ℝ) (ep:0<ε) :
    ∀ᶠ r in trail,∀ tp:0<r^a,∀ x:I → Cover,Plot C (P.b r) (P.middle r) (P.j r) x →
    ∀ z:C.label D,Cluster F Q J v r (P.b r) (P.j r) x z →
    ‖observed B J φ tp D (C.S.gridPoint (P.j r) ∘ x) (Frame.born J r v)-
      WilsonSeparatedMovingRichCharge.read B F J D φ (r^a) z‖≤ε*g r^k*r^D := by
  let m : ℝ := ∫ z : Points 2, ‖φ z‖
  have nonnegm : 0 ≤ m := integral_nonneg fun _=>norm_nonneg _
  let ε':=ε/(m+1)
  have ε'p:0<ε' := div_pos ep (by linarith)
  have bill : m*ε'≤ε := by
    calc
      _≤(m+1)*ε' := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) ε'p.le
      _=ε := by dsimp [ε'];field_simp [show m+1≠0 by linarith]
  let basis:=WilsonMacroscopicRichFree.basis C B D
  let W (i:Glyph B D) (_:Fin 1):=(basis i)
  have fee : (∑ j:Fin 1,((D:ℝ)+1)*(4*b))<1/32 := by simpa using reserve
  have grant (i:Glyph B D) := WilsonSeparatedOwnLength.original (de:=fun _:Fin 1=>D)
    F fac anchor Q P J lead v (W i) hg hG ap (ap.trans ab) edge fee k ε' ε'p
  filter_upwards [Filter.eventually_all.mpr grant,WilsonSeparatedMovingRichGeometry.original φ P ap ab edge,length_rate.pos,hg.positive] with r bills geom rp gp tp x plot z hz
  let near:=C.S.gridPoint (P.j r) ∘ x
  let ins:=Frame.born J r v
  let c:=ε'*g r^k*r^D
  have g0:0≤g r^k*r^D := mul_nonneg (pow_nonneg gp.le _) (pow_nonneg rp.le _)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg ep.le (pow_nonneg gp.le _)) (pow_nonneg rp.le _))).mpr
  intro i
  let w:=Frame.born J (r^a) (d:=fun _:Fin 1=>D) (W i)
  let A (y:Fin 1→E4):=whole V near ins y w
  let T (y:Fin 1→E4):=upon V D 0 y w (V.project D z)
  have left:observed B J φ tp D near ins i=∫ u,φ u*A (far (r^a) u) := zoom φ tp A
  have right:WilsonSeparatedMovingRichCharge.read B F J D φ (r^a) z i=∫ u,φ u*T (far (r^a) u) := by
    change (WilsonMacroscopicRichMeasuredGram.bank B F J D φ (r^a)).vecMul (WilsonMacroscopicRichRegister.coords B J (τ:=r^a) (V.project D z)) i=_
    rw [←WilsonMacroscopicRichRegister.read_field B F J φ tp i (V.project D z)]
    exact zoom φ tp T
  have hi:=integrable F φ (r^a) near ins w (fun u hu=>(geom u hu).2 x plot)
  have hj:=integrable F φ (r^a) (sole (0:E4)) (sole (V.project D z):Labels V (fun _:Unit=>D)) w
    (fun u hu=>single (Real.rpow_pos_of_pos rp _) u (geom u hu).1)
  change ‖observed B J φ tp D near ins i-
    WilsonSeparatedMovingRichCharge.read B F J D φ (r^a) z i‖≤_
  have hi' : Integrable (fun u=>φ u*A (far (r^a) u)) := hi
  have hj' : Integrable (fun u=>φ u*T (far (r^a) u)) := hj
  rw [left,right,←integral_sub hi' hj']
  have φi : Integrable (fun u:Points 2=>φ u) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have point (u:Points 2): ‖φ u*A (far (r^a) u)-φ u*T (far (r^a) u)‖≤‖φ u‖*c := by
    by_cases hu:u∈tsupport φ
    · have row:=((bills i x plot).2 z hz (far (r^a) u) (geom u hu).1 ((geom u hu).2 x plot)).1
      rw [←mul_sub,norm_mul];exact mul_le_mul_of_nonneg_left row (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hu]
  calc
    _≤ ∫ u,‖φ u‖*c := norm_integral_le_of_norm_le (φi.norm.mul_const c) (Eventually.of_forall point)
    _ = (m*ε')*(g r^k*r^D) := by rw [integral_mul_const];dsimp only [m,c];ring
    _ ≤ ε*(g r^k*r^D) := mul_le_mul_of_nonneg_right bill g0
    _ = _ := by simp only [id_eq];ring

end YM.Integration.WilsonSeparatedMovingRichCluster
