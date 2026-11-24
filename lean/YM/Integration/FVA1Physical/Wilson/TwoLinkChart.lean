import YM.Integration.FVA1Physical.Wilson.GaussianEntrance

/-! Every component of the actual log chart of a forest draw is a fixed
two-link product logarithm after a norm-one projection. Thus its derivatives
at zero have a single price for every forest, period and volume. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Lattice RG YM.Wilson Exterior Tree Precision
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f} (F:Forest S.ratio)
local notation "E" => Comparison.RG02.Bulk.Joint S F (G:=G)
local notation "V" => ℝ × (G.Color × G.Color)
local notation "Y" => ℝ × fieldDir G f 1

def linkChart (G:Gauge) (v:ℝ×(G.Color×G.Color)):ℝ×G.Color :=
  (v.1,G.plog (G.mat (G.lieExp v.2.1)*G.mat (G.lieExp v.2.2)))

theorem linkChart_smooth (G:Gauge):ContDiffAt ℝ ω (linkChart G) 0:=by
  apply contDiffAt_fst.prodMk
  have a:ContDiffAt ℝ ω (fun v:ℝ×(G.Color×G.Color)=>G.mat (G.lieExp v.2.1)) 0:=
    G.exp_jet.contDiffAt.comp _ (contDiffAt_fst.comp (f:=Prod.snd) _ contDiffAt_snd)
  have b:ContDiffAt ℝ ω (fun v:ℝ×(G.Color×G.Color)=>G.mat (G.lieExp v.2.2)) 0:=
    G.exp_jet.contDiffAt.comp _ (contDiffAt_snd.comp (f:=Prod.snd) _ contDiffAt_snd)
  let H:=fun v:ℝ×(G.Color×G.Color)=>G.mat (G.lieExp v.2.1)*G.mat (G.lieExp v.2.2)
  have home:H 0=1:=by simp [H]
  have outer:ContDiffAt ℝ ω G.plog (H 0):=home.symm ▸ G.plog_diff
  exact outer.comp _ (a.mul b)

private theorem chart_factor (j:Body 1 f) :
    ∃P:E→L[ℝ] V, (∀v,‖P v‖≤‖v‖) ∧ ∀v,
      ((fineLogChart F v).1,(fineLogChart F v).2 j)=linkChart G (P v) := by
  let T:E→L[ℝ]ℝ:=ContinuousLinearMap.fst ℝ _ _
  let f₀:E→L[ℝ] AxisChart G F:=(ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  let c₀:E→L[ℝ] fieldDir G c 1:=(ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  let e:Edge (Site f):=(j.1,axisEquiv.symm j.2)
  let m:Body 1 c:=(S.ratio.parent e.1,coord e.2)
  have data (v:E):‖T v‖≤‖v‖:=norm_fst_le ..
  by_cases trunk:e∈F.trunks
  · refine ⟨T.prod 0,fun v=>max_le (data v) (by simp),fun v=>?_⟩
    change (v.1,G.plog (G.mat (Work.F03.live F v.2 e)))=(v.1,G.plog (G.mat (G.lieExp 0)*G.mat (G.lieExp 0)))
    rw [show Work.F03.live F v.2 e=1 from F.on_tree _ ⟨e,trunk⟩];simp
  let A:E→L[ℝ]G.Color:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : F.Free=>G.Color) ⟨e,trunk⟩).comp f₀
  let B:E→L[ℝ]G.Color:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Body 1 c=>G.Color) m).comp c₀
  have costA(v:E):‖A v‖≤‖v‖:=(norm_le_pi_norm v.2.2 _).trans ((norm_snd_le v.2).trans (norm_snd_le v))
  have costB(v:E):‖B v‖≤‖v‖:=(norm_le_pi_norm v.2.1 _).trans ((norm_fst_le v.2).trans (norm_snd_le v))
  have loc(v:E):Work.F03.live F v.2 e=G.lieExp (A v)*replica S.ratio (represent v.2.1) e:=F.off_tree _ ⟨e,trunk⟩
  by_cases inner:S.ratio.parent (e.1+step e.2)=S.ratio.parent e.1
  · refine ⟨T.prod (A.prod 0),fun v=>max_le (data v) (max_le (costA v) (by simp)),fun v=>?_⟩
    change (v.1,G.plog (G.mat (Work.F03.live F v.2 e)))=(v.1,G.plog (G.mat (G.lieExp (A v))*G.mat (G.lieExp 0)))
    rw [loc,replica,if_pos inner];simp
  refine ⟨T.prod (A.prod B),fun v=>max_le (data v) (max_le (costA v) (costB v)),fun v=>?_⟩
  change (v.1,G.plog (G.mat (Work.F03.live F v.2 e)))=(v.1,G.plog (G.mat (G.lieExp (A v))*G.mat (G.lieExp (B v))))
  rw [loc,replica,if_neg inner,Work.F03.represent_link,G.mat_mul];rfl

def linkChartCost (G:Gauge) (k:ℕ):ℝ:=‖iteratedFDeriv ℝ k (linkChart G) 0‖

theorem fineChart_uniform (k:ℕ):‖iteratedFDeriv ℝ k (fineLogChart (G:=G) F) 0‖≤linkChartCost G k := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro w
  let u:= iteratedFDeriv ℝ k (fineLogChart F (G:=G)) 0 w
  let tariff:=linkChartCost G k*∏ i,‖w i‖
  have nn:0≤tariff:=mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _=>norm_nonneg _)
  have sm:ContDiffAt ℝ ω (fineLogChart (G:=G) F) 0:=contDiffAt_fst.prodMk
    ((Work.F03.inclusion_smooth F).snd.comp (f:=Prod.snd) (0:E) contDiffAt_snd)
  have cells (j:Body 1 f):‖(u.1,u.2 j)‖≤tariff:=by
    let Q:Y→L[ℝ]ℝ×G.Color:=(ContinuousLinearMap.fst ℝ _ _).prod
      ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Body 1 f=>G.Color) j).comp (ContinuousLinearMap.snd ℝ _ _))
    obtain ⟨P,cap,law⟩:=chart_factor (G:=G) F j
    have de:Q ∘ fineLogChart (G:=G) F=linkChart G ∘ P:=funext law
    have exactJet:Q u=iteratedFDeriv ℝ k (linkChart G) 0 (fun i=>P (w i)):=by
      change (Q.compContinuousMultilinearMap (iteratedFDeriv ℝ k (fineLogChart F) 0)) w=_
      have atP:ContDiffAt ℝ k (linkChart G) (P 0):=by rw [P.map_zero];exact (linkChart_smooth G).of_le le_top
      rw [← Q.iteratedFDeriv_comp_left sm le_top,de,Comparison.RG02.Assembly.contact_right P atP,P.map_zero]
      rfl
    change ‖Q u‖≤tariff
    rw [exactJet]
    exact ((iteratedFDeriv ℝ k (linkChart G) 0).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>cap (w i))) (norm_nonneg _))
  let j:Body 1 f:=(0,coord 0)
  change max ‖u.1‖ ‖u.2‖≤tariff
  exact max_le ((norm_fst_le (u.1,u.2 j)).trans (cells j))
    ((pi_norm_le_iff_of_nonneg nn).2 fun i=>(norm_snd_le (u.1,u.2 i)).trans (cells i))
end YM.Integration.FVA1Physical.Wilson
