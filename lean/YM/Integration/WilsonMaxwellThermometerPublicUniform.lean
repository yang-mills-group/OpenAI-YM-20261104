import YM.Integration.WilsonMaxwellThermometerPublicStation
/-! A period-independent position detector bound at a sufficiently wide
real reporting station, with the original three independent fine sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerPublicUniform
open Function Set Filter Finset Metric MeasureTheory Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonMaxwellThermometerFirstDetector WilsonMaxwellThermometerShiftedPanel
open WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open scoped Topology BigOperators Classical

open WilsonMaxwellThermometerPublicStation
variable {G : Gauge} (R : Run G) (W : Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)
variable (s:ℝ→ℕ)
local notation "μ" => (fun (r : ℝ) (per : ℕ) =>
  chart R (s r) per (aperture R s r) (granted R s r))

def Spacious:Prop:=∀d:ℕ,Tendsto (fun r=>(aperture R s r)^d*((R.family.S.denominator (s r)).val:ℝ)) trail atTop

theorem boards (small:Tendsto (aperture R s) trail (𝓝 0))(room:Spacious R s)
    {U:Set Mesh}(good:U∈Front):∀ᶠ r in trail,∀p:ℕ, μ r p∈U:=by
  let F:Filter (ℝ×ℕ):=Filter.comap Prod.fst trail
  have radius:Tendsto (Prod.fst:ℝ×ℕ→ℝ) F trail:=tendsto_comap
  have paid:Tendsto (fun z:ℝ×ℕ=>μ z.1 z.2) F Front:=by
    apply Cirrus.goesFront
    constructor
    · exact small.comp radius
    · intro d
      apply tendsto_atTop_mono _ ((room d).comp radius)
      intro z
      have cost:((R.family.S.denominator (s z.1)).val:ℝ)≤((R.family.side (s z.1) z.2).val:ℝ):=by
        exact_mod_cast Nat.le_mul_of_pos_left _ (R.family.S.period z.2).pos
      exact mul_le_mul_of_nonneg_left cost (pow_nonneg (granted R s _).le d)
  exact (eventually_comap.mp (paid.eventually good)).mono fun r hr p=>hr (r,p) rfl

theorem tested_at (small:Tendsto (aperture R s) trail (𝓝 0))(room:Spacious R s)
    (p:Tags G 6 3)(δ:ℝ)(pos:0<δ):
    ∀ᶠ r in trail,∀N per,s r≤N→dist
      (report R W K s r (N,per) p) ((Rose.test K).applyTo (fun x=>continuum W (V:=V) x p))≤
        (∫x:Points 3,‖Rose.test K x‖)*δ:=by
  filter_upwards [self_mem_nhdsWithin (s:=Set.Ioi 0),
    boards R s small room (nearby W K p pos)] with r hr due
  intro N per live
  let z:= (N,per)
  let g:=R.family.S.toDepth live per
  let a:=μ r per
  let χ:=positions (R:=R) r z
  let sample:=fun o=>atSites W (V:=V) a (g.parent ∘ o) p
  have cash (x)(hx:x∈tsupport (Rose.test K)):dist (sample (χ x)) (continuum W (V:=V) x p)≤δ:=by
    obtain ⟨v,hs,good⟩:=WilsonMaxwellThermometerParentLift.parents R.family.S live per hr x
    have agree:atSites W (V:=V) a (g.parent ∘ χ x)=sampled W (V:=V) (translated a v):=by
      apply same_sites;refine Eq.trans ?_ hs.symm;funext i;exact wrap_lift _
    dsimp only [sample]
    rw [agree]
    apply due per x hx
    simpa only [a,chart,aperture,if_pos (show 0<r from hr)] using good
  have bill:=WilsonMaxwellThermometerFirstCells.test_price W K χ (placed (R:=R) r z) sample p δ cash
  rw [tested (Rose.test K) χ (placed (R:=R) r z) sample] at bill
  rw [←quotient,dist_eq_norm,WilsonMaxwellThermometerPublicStation.filed,dif_pos live,_root_.sum_apply]
  simpa only [_root_.smul_apply,smul_eq_mul] using bill

theorem basis {I:Fin 3→Type} [∀i,Fintype (I i)](f:∀i,I i→Sec G 6)
    (small:Tendsto (aperture R s) trail (𝓝 0))(room:Spacious R s):
    ∃C:ℝ,0≤C ∧ ∀ᶠ r in trail,∀N per, s r≤N→∀a:∀i,I i,
      ‖report R W K s r (N,per) (fun i=>f i (a i))‖≤C:=by
  let money:=fun a:∀i,I i=>‖(Rose.test K).applyTo (fun x=>continuum W (V:=V) x (fun i=>f i (a i)))‖
  let M:=∫x:Points 3,‖Rose.test K x‖
  have mp:0≤M:=integral_nonneg fun x=>norm_nonneg _
  refine ⟨(∑a,money a)+M,add_nonneg (Finset.sum_nonneg fun _ _=>norm_nonneg _) mp,?_⟩
  have all:∀ᶠ r in trail,∀a:∀i,I i,∀N per,s r≤N→
      dist (report R W K s r (N,per) (fun i=>f i (a i)))
        ((Rose.test K).applyTo (fun x=>continuum W (V:=V) x (fun i=>f i (a i))))≤M*1:=
    eventually_all.mpr fun a=>tested_at R W K s small room _ 1 zero_lt_one
  filter_upwards [all] with r funded
  intro N per live a
  have b:=norm_le_insert' (report R W K s r (N,per) (fun i=>f i (a i)))
      ((Rose.test K).applyTo (fun x=>continuum W (V:=V) x (fun i=>f i (a i))))
  have fee:money a≤∑b,money b:=Finset.single_le_sum (f:=money) (fun i _=>norm_nonneg _) (Finset.mem_univ a)
  apply b.trans
  exact add_le_add fee (by simpa only [dist_eq_norm,mul_one] using funded a N per live)

end YM.Integration.WilsonMaxwellThermometerPublicUniform
