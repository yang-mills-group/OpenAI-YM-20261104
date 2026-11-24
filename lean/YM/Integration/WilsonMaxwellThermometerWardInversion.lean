import YM.Integration.WilsonMaxwellThermometerWardPair

/-! Exact unregraded Ward hearing on the whole finite even inversion
regulator with its true source, independently placed spectator and orbit Haar.
The receptor states explicitly which source and spectator bonds are clear. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardInversion
open Function Set Filter MeasureTheory Lattice Wilson Push.Mark PertExtension.Orb
open WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
open WilsonMaxwellThermometerWardSampler WilsonMaxwellThermometerWardPair
open scoped Classical Topology
variable {G:Gauge} {n:Side}
local notation "H" => WilsonMaxwellThermometerWardConditional.law G

theorem original {r M:ℕ} (nEven:Even n.val) (cut:M≤n.val) (o:Site n)
    (span:2*r+4<separation o (-o)) {f:Pre G} (hf:Continuous f) (paid:MicroAt f r M)
    {S T:Set (Site n)} (source:LocalOn S (f ∘ expandAt o))
    (clear:∀e:Edge (Site n),e.1∈S→e.1+step e.2∈S→far r o (reflect e))
    {K:Config G n→ℂ} (hk:Continuous K) (readK:LocalOn T K)
    (room:∀e:Edge (Site n),e.1∈T→e.1+step e.2∈T→far r o e ∧ far r o (reflect e))
    (s:ℝ) (hs:s≠0):
    (∫q:OEdge n→G.El,(preDensity s (liftLinks q):ℂ)*(f (expandAt o (liftLinks q))*K (liftLinks q)) ∂H)=0:=by
  let paint:=fun q:OEdge n→G.El=>(preDensity s (liftLinks q):ℂ)*(f (expandAt o (liftLinks q))*K (liftLinks q))
  have tilt:Continuous (preDensity (G:=G) (n:=n) s):=Real.continuous_exp.comp (((energy_cont.div_const 2).neg).div_const (s^2))
  have hp:Continuous paint:=((Complex.continuous_ofReal.comp tilt).mul ((onStencil o hf).mul hk)).comp (lift_cont _)
  let showAll:=fun yz:Held G r o×Free G r o=>emit r o ((chamber r o).symm yz)
  have showCont:Continuous showAll:=(continuous_emission r o).comp (chamber r o).symm.continuous
  let D:=MeasurableEquiv.piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.El) (far r o)
  have hD:MeasurePreserving D (prior G n) ((H).prod H):=
    measurePreserving_piEquivPiSubtypeProd (fun _:Edge (Site n)=>G.probHaar) (far r o)
  have push:MeasurePreserving showAll ((H).prod H) H:=(funded r o).comp hD.symm
  have whole:(∫q,paint q ∂H)=∫yz,paint (showAll yz) ∂(H).prod H:=by
    rw [←push.map_eq,integral_map push.measurable.aemeasurable hp.aestronglyMeasurable]
  change (∫q,paint q ∂H)=0
  have adm:Integrable (fun yz:Held G r o×Free G r o=>paint (showAll yz)) ((H).prod H):=
    (hp.comp showCont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [whole,integral_prod _ adm]
  suffices each : ∀y:Held G r o,(∫v:Free G r o,paint (showAll (y,v)) ∂H)=0 by simp_rw [each,integral_zero]
  intro y
  let B:=base r o y
  have bfix:mirror B=B:=reflected nEven _
  have single_field (v:Free G r o) (e:Edge (Site n)) (farTwin:far r o (reflect e)) :
      supplied r o y v e=single r o B v e:=by
    rw [fixed r o nEven (WilsonMaxwellThermometerWardClear.original r o span).2]
    change (if far r o e then mirror (single r o B v) e else single r o B v e)=_
    by_cases h:far r o e
    · rw [if_pos h]
      exact (congrArg Inv.inv (held r o B v _ farTwin)).trans ((congrFun bfix e).trans (held r o B v e h).symm)
    · exact if_neg h
  have src(v:Free G r o):f (expandAt o (supplied r o y v))=f (expandAt o (single r o B v)):=
    source _ _ fun e h k=>single_field v e (clear e h k)
  have ext(v:Free G r o):K (supplied r o y v)=K B:=readK _ _ fun e h k=>
    (single_field v e (room e h k).2).trans (held r o B v e (room e h k).1)
  let c:ℂ:=(Real.exp ((s^2)⁻¹/2*energy B):ℂ)*K B
  have row(v:Free G r o):paint (showAll (y,v))=
      c*((bare ((s^2)⁻¹) (single r o B v):ℂ)*f (expandAt o (single r o B v))):=by
    change (preDensity s (supplied r o y v):ℂ)*(f (expandAt o (supplied r o y v))*K (supplied r o y v))=_
    rw [density r o nEven span,src,ext,Complex.ofReal_mul]
    dsimp only [c,B]
    ring
  simp_rw [row,integral_const_mul]
  have debt:=WilsonMaxwellThermometerWardConditional.original hf paid o cut (inv_ne_zero (pow_ne_zero 2 hs)) (((chamber r o) B).1)
  change (∫v:Free G r o,(bare ((s^2)⁻¹) (single r o B v):ℂ)*f (expandAt o (single r o B v)) ∂H)=0 at debt
  rw [debt,mul_zero]

end YM.Integration.WilsonMaxwellThermometerWardInversion
