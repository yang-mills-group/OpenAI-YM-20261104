import YM.Integration.WilsonCoherentMayerPriorLog

/-! A uniform before-cutoff comparison of the complete independently filed marked logarithm once its original numerator has been estimated on all submodes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorBank
open Function Filter Finset RG Source Marker Extra.Trajectories
open LocalComparison PhysicalNext.Repeat.Legato
open Filter Finset Function Lattice Wilson RG Precision Source Marker Push.GridApprox
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open FullQLocal FullQLocal.RenderedStep Comparison.RG02 WilsonLimitConstruction
open RG3.Script.Picnic
open IterationFour.Vacuum MergeProof MergeProof.Accent
open MS MS.Menus MS.Local.Physical Extra.Histories ActualOriginalQReaders

open WilsonCoherentMayerPriorCapacity WilsonCoherentMayerPriorLog WilsonCoherentMayerPriorSource
open scoped Classical BigOperators
variable {V:Type}[DecidableEq V][Fintype V][Nonempty V]

omit [Fintype V] [Nonempty V] in
private lemma scale (Γ:Census V){C b:ℝ}(cp:0<C)(root:1≤b)(e:ℕ):
    bill Γ (C*b^e)≤bill Γ C * b^(e+e*degree Γ):=by
  have bn:0≤b:=zero_le_one.trans root
  have atOne:1≤b^e:=one_le_pow₀ root
  have seen:0≤count Γ:=by unfold count;exact Finset.sum_nonneg (fun _ _=>by positivity)
  unfold bill
  calc
    _≤2*((1+C)*b^e)*count Γ*(((1+2*C)*b^e)^degree Γ):=by
      gcongr <;> nlinarith only [atOne]
    _=_:=by rw [pow_add,pow_mul,mul_pow];ring

variable {G:Gauge}{B:Deck G}(R:Run G)(simple:G.Simple)(u:V→MS.Rake.Label B)
    (J:Request V)(Q:MS.Land.Prescription B)(μ:ℝ)

/-- All companions in the logarithm come from the actual arrived source. The independent mark is recorded additively with the normalized log of its full filed residual. -/
theorem original (K:ℕ):∃C:ℝ,0<C ∧ ∃e:ℕ,∀ᶠt:ℕ in atTop,
    ∀(d:LocalFormal.Datum R.family (Stock.census V)),d.level=t→d.cutoff=d.level+1→
    (∀a:Slot u,R.family.ref a.2.size≤d.level+1)→
    ∀(o:V→Lattice.Site (R.family.side (d.level+1) d.period))(ks:V→ℕ), (∀i,ks i≤K)→
    ∀(x:IndependentTests (ActualOriginalQPointSetup.request R u J).tests){j:ℕ}(live:j≤d.level+1)
      (U:Config G (R.family.side j d.period)) (q old:Poly (Stock.census V)),q.part (Stock.census V).quiet=0→
    let actual:=physical R simple u J Q μ d o ks x live U
    ∀{δ:ℝ},0≤δ→δ≤1/2→(∀s,‖actual.part s-(Poly.pass q*old).part s‖≤δ)→
      old.part (Stock.census V).quiet≠0 ∧ ∀s,
        ‖(connected actual-(q+connected (normalized old))).part s‖≤C*(R.family.path.levels.clock.hatBeta t)^e*δ:=by
  let Γ:=Stock.census V
  obtain ⟨c,cp,e,prev⟩:=WilsonCoherentMayerPriorSource.original R simple u J Q μ K
  have cn:0≤count Γ:=by unfold count;exact Finset.sum_nonneg fun _ _=>by positivity
  have fund:0≤bill Γ c:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one cp.le)) cn)
    (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) cp.le)) _)
  refine ⟨1+bill Γ c,add_pos_of_pos_of_nonneg zero_lt_one fund,e+e*degree Γ,?_⟩
  filter_upwards [prev] with t bounds
  intro d date top age o ks law x j live U q old quiet actual δ dp half fit
  let b:=R.family.path.levels.clock.hatBeta t
  have one:1≤b:=(R.family.path.levels.fits.delayed t).le
  have capital:=bounds d date top age o ks law x live U
  have full:=paid actual (Poly.pass q*old) capital.1 dp half (mul_nonneg cp.le (pow_nonneg (zero_le_one.trans one) _)) capital.2 fit
  have detached:old.part Γ.quiet≠0:=by
    simpa only [Poly.quiet_mul,Poly.pass_part _ quiet,one_mul] using full.1
  refine ⟨detached,fun s=>?_⟩
  rw [←filed q old quiet detached]
  calc _≤δ*bill Γ (c*b^e):=full.2 s
       _≤δ*(bill Γ c*b^(e+e*degree Γ)):=mul_le_mul_of_nonneg_left (scale Γ cp one e) dp
       _≤(1+bill Γ c)*b^(e+e*degree Γ)*δ:=by
         rw [mul_comm δ]
         exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
           (pow_nonneg (zero_le_one.trans one) _)) dp

end YM.Integration.WilsonCoherentMayerPriorBank
