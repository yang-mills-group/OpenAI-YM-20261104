import YM.Integration.WilsonGeneralReducedPhysicalSelfGappedHome
import YM.Integration.WilsonGeneralReducedPhysicalSelfQuadrature

/-! The smooth signed determining packet is integrated against the released
finite Wilson word. Its complete thermal vote is restored before the measured
coordinates are frozen. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfGappedSmooth
open MeasureTheory Function Filter Finset Set Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register Trace.Pilot PhysMS Frame XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonGeneralReducedPhysicalSelfGappedBoard (atPlace)
open WilsonGeneralReducedPhysicalSelfFullWord (finiteWord atNode)
open WilsonOriginalPublicPlantedGram (measured)
open WilsonPositionProgramPublicContrast (assay)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonGeneralReducedPhysicalSelfThermal (suspended salary)
open private placed from YM.Integration.WilsonGeneralReducedPhysicalSelfMeasure
open private oneSite from YM.Integration.WilsonGeneralReducedPhysicalSelfThermal
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G){g:G.Simple}{M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T:Prescription (Press.portDeck G)}{dial:Bool}(H:Main.Match Z g M T dial){Y:(Bel R.family.book).Hierarchy}
    {l:Filter (ℕ×ℕ)}(B:Deck G)(h:ℕ)(a:Axis)
local notation "I" => Glyph B h

private theorem measurableWords (M:Mesh)(c:Four ℝ){E:Type*}[MeasurableSpace E](read:pack 2→E):
    Measurable (fun y:Points 2=>read (draw y M c)):=by
  apply (measurable_of_countable read).comp
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply Int.measurable_ceil.comp
  change Measurable (fun y:Points 2=>(y+Mesh.room c : Points 2) i j/M.spacing)
  fun_prop

private theorem sampled {p:Points 2}(b:ContDiffBump p)(f:Points 2→ℂ)(mf:Measurable f){C:ℝ}
    (bound:∀y,b.normed volume y≠0→‖f y‖≤C):Integrable (fun y=>b.normed volume y • f y):=by
  have hw:Integrable (b.normed volume):=b.integrable_normed
  apply (hw.mul_const C).mono' (hw.aestronglyMeasurable.smul mf.aestronglyMeasurable)
  apply ae_of_all
  intro y
  change ‖b.normed volume y • f y‖≤_  
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg_normed y)]
  by_cases hz:b.normed volume y=0
  · simp [hz]
  exact mul_le_mul_of_nonneg_left (bound y hz) (b.nonneg_normed y)

private theorem integrated {p:Points 2}(b:ContDiffBump p)(f h:Points 2→ℂ)(mf:Measurable f)(mh:Measurable h)
    {C δ:ℝ}(ground:∀y,b.normed volume y≠0→‖h y‖≤C)(rest:∀y,b.normed volume y≠0→‖f y-h y‖≤δ):
    ‖(∫y:Points 2,b.normed volume y • f y)-(∫y:Points 2,b.normed volume y • h y)‖≤δ:=by
  have hg:=sampled b h mh ground
  have hf:=sampled b f mf (C:=δ+C) (fun y hy=>by
    calc ‖f y‖=‖(f y-h y)+h y‖:=by rw [sub_add_cancel]
         _≤_ := (norm_add_le ..).trans (add_le_add (rest y hy) (ground y hy)))
  rw [←integral_sub hf hg]
  simp_rw [←smul_sub]
  have hi:=sampled b (fun y=>f y-h y) (mf.sub mh) rest
  calc
    _≤∫y:Points 2,‖b.normed volume y • (f y-h y)‖:=norm_integral_le_integral_norm _
    _≤∫y:Points 2,b.normed volume y*δ:=by
      apply integral_mono_ae hi.norm (b.integrable_normed.mul_const δ)
      apply ae_of_all
      intro y
      change ‖b.normed volume y • (f y-h y)‖≤_  
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (b.nonneg_normed y)]
      by_cases hz:b.normed volume y=0
      · simp [hz]
      exact mul_le_mul_of_nonneg_left (rest y hz) (b.nonneg_normed y)
    _=δ:=by rw [integral_mul_const,b.integral_normed,one_mul]

theorem thermal {p:Points 2}(b:ContDiffBump p)(j q:ℕ){cap:ℕ}(P:Handoff.Directory Z j cap)(u:ℝ)(c:Four ℝ)
    (D:I→PowerSeries ℂ)(room:Handoff.Directory.budget G 2 h+q≤cap)(cold:|u|≤1)(fee:ℝ)
    (paid:∀y:Points 2,b.normed volume y≠0→salary Z a j q (atPlace (Z.run.step j) c y) D≤fee):
    ‖(∫ y:Points 2,b.normed volume y • cash q u (suspended Z a j (atPlace (Z.run.step j) c y) D))-
      (∫ y:Points 2,b.normed volume y • cash q u (finiteWord Z a j (atPlace (Z.run.step j) c y) (fun i=>cash q u (D i))))‖≤
        3*|u|^(q+1)*fee:=by
  let M:=Z.run.step j
  let v:=fun i=>cash q u (D i)
  let value (s:Sample 2):ℂ:=cash q u (finiteWord Z a j s v)
  let mass (z:Fin 2→M.Sites):ℝ:=‖value (placed M c z)‖
  have charge(y:Points 2):‖value (atPlace M c y)‖≤∑z,mass z:=by
    calc
      _=mass (chartV (atPlace M c y)):=congrArg norm (oneSite Z a j q P (atPlace M c y) v u rfl room)
      _≤_:=single_le_sum (f:=mass) (fun z _=>norm_nonneg _) (mem_univ (chartV (atPlace M c y)))
  apply integrated b _ _
    (measurableWords M c (fun z=>cash q u (suspended Z a j ⟨M,z,c⟩ D)))
    (measurableWords M c (fun z=>value ⟨M,z,c⟩)) (fun y _=>charge y)
  intro y hy
  exact (WilsonGeneralReducedPhysicalSelfThermal.one Z a j q P (atPlace M c y) D u rfl room cold).trans
    (mul_le_mul_of_nonneg_left (paid y hy) (by positivity))

include H in
theorem original (lead:Leading F J)(obedient:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(below:l≤f.fuse):
    ∃(p:Points 2)(b:ContDiffBump p)(σ k:ℝ),0<σ ∧ 0<k ∧ (∀y∈tsupport b,∀i:Axis,σ<y 1 i-y 0 i) ∧
    (∀x:RG17.Free R.family h,∃A:ℝ,0≤A ∧ ∀ᶠr in trail,∀(arm:Arm R.family S l h (homogeneous F J Z r h x)),
      ∀{ι:Type}[Fintype ι](s:ℕ)(o:ι→Fin 2 → Lattice.Cover)(y:ι→Points 2)(μ:ι→ℂ),
      (∀i,y i∈tsupport b) → (∀i,Order.grid R.family s (o i)=r • y i) → (∀i,Order.grid R.family s (o i)∈conf 2) →
      ∀ε:ℝ,0<ε → ∀ᶠ n:ℕ×ℕ in l,∀z:ι → Lattice.Cover,‖∑i,μ i*
        physical (grades h h) s (fun l=>o i l+z i) n.1 n.2 (columns R a h h (arm.source n) (arm.source n))‖≤
          (∑i,‖μ i‖)*A+ε) ∧
    ∀q:ℕ,∀(L:Filter ℝ){t:ℝ→ℝ},(∀ᶠr in L,0<t r) → Tendsto t L (𝓝 0) →
    ∀(D:ℕ)(C:ℝ),∃j₀:ℕ,∀ᶠ r in L,∀j≥j₀,(j:ℝ)≤C*(-Real.log (t r))^D →
    ∀{cap}(_:Handoff.Directory Z j cap),Handoff.Directory.budget G 2 h+q≤cap →
    ∀c∈(Z.run.step j).Box,∀u:ℝ,|u|≤8*t r →
    ∀v:I→ℂ,k*‖v‖^2≤‖∫y:Points 2,b.normed volume y •
      cash q u (finiteWord Z a j (atPlace (Z.run.step j) c y) v)‖:=by
  obtain ⟨p,b,σ,k,sp,kp,gaps,real,margin⟩:=
    WilsonGeneralReducedPhysicalSelfGappedHome.original R F J Z H B h a lead obedient below
  refine ⟨p,b,σ,k,sp,kp,gaps,real,?_⟩
  intro q L t pos small D C
  obtain ⟨j₀,paid⟩:=margin q L pos small D C
  refine ⟨j₀,?_⟩
  filter_upwards [paid] with r due j later short cap P room c box u heat v
  let M:=Z.run.step j
  have sale:=due j later short P room c box u heat
    (WilsonGeneralReducedPhysicalSelfQuadrature.weight M c b)
    (WilsonGeneralReducedPhysicalSelfQuadrature.representative M c b)
    (WilsonGeneralReducedPhysicalSelfQuadrature.positive M c b)
    (WilsonGeneralReducedPhysicalSelfQuadrature.total M c b)
    (WilsonGeneralReducedPhysicalSelfQuadrature.inside M c b) v
  rw [WilsonGeneralReducedPhysicalSelfQuadrature.original c b Z a j q P room u v]
  exact sale

end YM.Integration.WilsonGeneralReducedPhysicalSelfGappedSmooth
