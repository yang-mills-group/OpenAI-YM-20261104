import YM.Integration.WilsonIndependentSpoutOrdinarySpring
import YM.Integration.WilsonIndependentSpoutHaarTree

/-! The odd-volume block forest retains exactly those ordinary Haar links
which are free in the chosen tree section of each cell. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrdinaryHaar
open Filter Set Lattice RG Exterior WilsonCoeffUV WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Prim
open RegulatorIR.Laplace RegulatorIR.Binding RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open PertExtension PertExtension.Orb WilsonIndependentSpoutOrdinaryPlate
open WilsonIndependentSpoutOrdinarySpring
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{f c:Side}(S:StepData c f)(F:Tree.Forest S.ratio)

def color {n:Side}(u:TreeVars G n)(p:Edge (Site n)):G.Color :=
  (cloth G n).symm u (p.1,coord p.2)

def Sliced (u:TreeVars G f):Prop:=∀ p∈F.trunks,color u p=0

theorem timber_at {n:Side}(u:TreeVars G n)(p:Edge (Site n)):
    timber G (sample u) (WilsonIndependentSpoutOrdinarySpring.peg p)=color u p := by
  ext j;simp [timber,sample,WilsonIndependentSpoutOrdinarySpring.peg,color]

theorem at_fare (sq:Square F)(u:TreeVars G f)(slice:Sliced S F u)(b:TreeVars G c)
    (p:Edge (Site f))(t:ℝ):
    flank (carnal S F (WilsonIndependentSpoutOrdinarySpring.peg p)) (joined u b) t=entry G (t • color u p) := by
  have place:branch F (resolve f (WilsonIndependentSpoutOrdinarySpring.peg p)) ↔ p∈F.trunks:=by
    rw [resolve,home];exact bone sq p
  change (if branch F (resolve f (WilsonIndependentSpoutOrdinarySpring.peg p)) then 0 else entry G (timber G (t • sample u) (WilsonIndependentSpoutOrdinarySpring.peg p)))=_
  rw [←WilsonIndependentSpoutOrdinaryPlate.dilate,timber_at]
  by_cases h:p∈F.trunks
  · rw [if_pos (place.mpr h),slice _ h,smul_zero,ent_zero]
  · rw [if_neg (fun r=>h (place.mp r))]
    unfold color;rw [map_smul];rfl

theorem original (sq:Square F)(N:Scale){T:Branchix→Orders (KFoot G)}(V:Sphere S F N T)
    (u:TreeVars G f)(slice:Sliced S F u)(b:TreeVars G c)(e:ℕ)(pos:0<e):
    (∑ p:Edge (Site f),drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e) e (joined u b)) =
      PowerSeries.coeff e (tale (fun t:ℝ=>unhaar (XSpace.Bare.chart G) (t • u))) := by
  have one (p:Edge (Site f)):
      drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e) e (joined u b)=PowerSeries.coeff e
        (tale (flank (carnal S F (WilsonIndependentSpoutOrdinarySpring.peg p)) (joined u b))):=by
    simpa only [dry,barkN,Prim.prism,Sum.elim_inl,one_mul,Nat.add_zero] using
      (V (.inl (WilsonIndependentSpoutOrdinarySpring.peg p))).figures (joined u b) pos
  simp_rw [one]
  rw [←map_sum,←tale_sum _ _ (fun p _=>(rooted S F (WilsonIndependentSpoutOrdinarySpring.peg p)).some.smooth_v _)]
  apply congrArg (PowerSeries.coeff e)
  symm
  apply tale_eq
  · have H:ContDiffAt ℝ ∞ (fun t:ℝ=>∑ p:Edge (Site f),flank (carnal S F (WilsonIndependentSpoutOrdinarySpring.peg p)) (joined u b) t) 0:=
      ContDiffAt.sum fun p _=>(rooted S F (WilsonIndependentSpoutOrdinarySpring.peg p)).some.smooth_v _
    convert H using 1;ext t;exact Finset.sum_apply _ _ _
  · have healthy (p:Edge (Site f)):∀ᶠ t:ℝ in 𝓝 0,
        entry G (t • color u p)=Real.log ((XSpace.Bare.chart G).J (t • color u p)):=by
      have h:Continuous (fun t:ℝ=>t • color u p):=continuous_id.smul continuous_const
      have ht:Tendsto (fun t:ℝ=>t • color u p) (𝓝 0) (𝓝 0):=by simpa only [zero_smul] using h.tendsto 0
      exact ht.eventually WilsonIndependentSpoutHaar.link
    filter_upwards [eventually_all.mpr healthy] with t ht
    rw [Finset.sum_apply,unhaar]
    simp_rw [at_fare S F sq u slice b,ht]
    apply Finset.sum_congr rfl
    intro i _
    unfold dij dyes color
    rw [(coatC G).apply_symm_apply,map_smul]
    rfl

end YM.Integration.WilsonIndependentSpoutOrdinaryHaar
