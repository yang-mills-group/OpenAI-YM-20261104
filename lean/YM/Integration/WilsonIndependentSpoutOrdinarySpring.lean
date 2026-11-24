import YM.Integration.WilsonIndependentSpoutOrdinaryPlate
import YM.Integration.WilsonIndependentSpoutSpringJets

/-! The actual outgoing spring on arbitrary ordinary periodic inputs,
retaining the two arguments and the same centered predictor before Wick. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOrdinarySpring
open Set Filter Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue RegulatorIR
open RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Laplace
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal PertExtension
open WilsonIndependentSpoutOrdinaryPlate
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{f c:Side}(S:StepData c f)

def peg {n:Side}(p:Edge (Site n)):Edge Cover:=(lift p.1,p.2)

theorem home {n:Side}(p:Edge (Site n)):around n (peg p)=p := by
  rcases p with ⟨v,a⟩;simp [around,peg]

theorem periodic {n:Side}(u:TreeVars G n):win G (sample u)=mantle u ∘ around n := by
  rw [links];funext i;simp [expandAt,around]

def joined (u:TreeVars G f)(b:TreeVars G c):KFoot G → ℝ:=Sum.elim (sample u) (sample b)

theorem at_fare (N:Scale)(p:Edge (Site c))(u:TreeVars G f)(b:TreeVars G c)(t:ℝ):
    flank (opi S N (peg p)) (joined u b) t = N.beta t*S.kernel.penalty*
      G.price (mantle (t • b) p*(S.prediction (mantle (t • u)) (directive S) p)⁻¹) := by
  change N.beta t*S.kernel.penalty*G.price
      (win G (t • sample b) (peg p)*(pond S.patch S.kernel (win G (t • sample u)) (peg p))⁻¹)=_
  simp_rw [←WilsonIndependentSpoutOrdinaryPlate.dilate,periodic]
  rw [river,Function.comp_apply,home]

def tuple (u:TreeVars G f)(b:TreeVars G c):Lawn (Joint G f c):=Sum.elim u b

theorem positive (h:S.patch.Branches S.kernel G)(N:Scale)(u:TreeVars G f)(b:TreeVars G c):
    (∑ p:Edge (Site c),tale (flank (opi S N (peg p)) (joined u b)))=
      tale (fun t:ℝ=>N.beta t*jointPen G S (t • tuple u b)) := by
  have hg:Tendsto (fun t:ℝ=>mantle (t • u)) (𝓝 0) (𝓝 1):=by
    have hc:Continuous (mantle : TreeVars G f → Wilson.Config G f):=by
      apply continuous_pi;intro i
      simp only [mantle,Work.F03.represent_link]
      exact G.lieExp_cont.comp ((continuous_apply _).comp (cloth G f).symm.continuous)
    have ht:Continuous (fun t:ℝ=>t • u):=continuous_id.smul continuous_const
    simpa only [Function.comp_def,zero_smul,mantle_zero] using (hc.comp ht).tendsto 0
  rw [←tale_sum _ _ (fun p _=>(locally S h N (peg p)).some.smooth_v _)]
  symm
  apply tale_eq
  · have H:ContDiffAt ℝ ∞ (fun t:ℝ=>∑ p:Edge (Site c),flank (opi S N (peg p)) (joined u b) t) 0:=
      ContDiffAt.sum fun p _=>(locally S h N (peg p)).some.smooth_v _
    convert H using 1;ext t;exact Finset.sum_apply _ _ _
  · filter_upwards [hg.eventually (Work.F04.prediction_germ h (tac S) (directive S))] with t hp
    rw [Finset.sum_apply]
    simp_rw [at_fare]
    change N.beta t*(S.kernel.penalty*
      (∑ i,G.price (mantle (t • b) i*(S.prediction (mantle (t • u)) (tac S) i)⁻¹)))=_
    rw [hp,←Finset.mul_sum];ring

theorem original (F:Tree.Forest S.ratio)(h:S.patch.Branches S.kernel G)(N:Scale)
    {T:Branchix→Orders (KFoot G)}(V:Sphere S F N T)
    (u:TreeVars G f)(b:TreeVars G c)(e:ℕ)(pos:0<e):
    (∑ p:Edge (Site c),drums (T (.inr (peg p)) e) (e+2) (joined u b))=
      -PowerSeries.coeff (e+2) (tale (fun t:ℝ=>N.beta t*jointPen G S (t • tuple u b))) := by
  have one (p:Edge (Site c)):
      drums (T (.inr (peg p)) e) (e+2) (joined u b)= -PowerSeries.coeff (e+2)
        (tale (flank (opi S N (peg p)) (joined u b))):=by
    simpa only [dry,barkN,Prim.prism,Sum.elim_inr,neg_one_mul] using (V (.inr (peg p))).figures (joined u b) pos
  simp_rw [one]
  rw [Finset.sum_neg_distrib,←map_sum,positive S h N]

end YM.Integration.WilsonIndependentSpoutOrdinarySpring
