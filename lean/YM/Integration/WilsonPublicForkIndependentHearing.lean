import YM.Integration.WilsonPublicForkTestProduct

/-! The actual reflected two-coordinate test on the independent program.
Both ordinary scalar types and every fitted output use the same near clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentHearing
open Filter Function Set Finset MeasureTheory PowerSeries FVA2 FVA2.O FVA2.O.Score FVA2.O.Enh
open FVA2.O.Project FVA2.Scale FVA2.Register Maxwell XSpace XSpace.Normalize
open MS MS.Land MS.Fleet MS.Theater MS.Rake PhysMS Trace.Pilot
open WilsonMSDictionaryFarRead WilsonPublicForkIndependentWindow
open WilsonPublicForkIndependentPlacement WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open WilsonPublicForkTestProduct
open scoped Classical Topology BigOperators
variable {G:Gauge}{n h:ℕ}
  (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
  {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

theorem continuous_cut {X:Type}[TopologicalSpace X]{K:Set X}{u:X→PowerSeries ℂ}
    (q:ℕ)(t:ℝ)(each:∀ k∈range (q+1),ContinuousOn (fun x=>coeff k (u x)) K):
    ContinuousOn (fun x=>cutoff q t (u x)) K:=by
  exact continuousOn_finsetSum _ (fun k hk=>continuousOn_const.mul (each k hk))

include ν ms in
theorem converted_profile (q:ℕ)(g:ℝ)(u:Scan G n)(ψ:Test n)(b:Dframe.Toon G h):
    ψ.applyTo (fun x=>cutoff q g (front Z u b x))=
    cutoff q g (converted Z M ν u ψ (Dframe.flash b)):=by
  rw [converted_eq Z M ν ms]
  change ψ.applyTo (fun x=>∑i∈range (q+1),(g:ℂ)^i*coeff i (front Z u b x))=_
  rw [Read.smear_sum]
  · unfold cutoff;simp only [Canon.Yield,Read.smearing,coeff_mk,Read.smear_one]
  · intro i _;exact continuousOn_const.mul ((((ms.separatedOPE ν).wilson.far u).2.1 _ i).mono ψ.tsupport_subset)

def ordinary (q:ℕ)(g s:ℝ)(u:Scan G n)(v:Scan G 1)(ψ:Test n)(φ:Test 2):ℂ:=
  tested ψ φ (fun p=>fee s (-(totalG v:ℝ))*cutoff q g (joint Z u v p.1 (relative p.2) s))

def two (q:ℕ)(g s:ℝ)(v:Scan G 1)(b:Dframe.Toon G h)(φ:Test 2):ℂ:=
  φ.applyTo (fun z=>fee s (-(totalG v:ℝ))*cutoff q g (leg Z v b (relative z) s))

include ν ms in
theorem original (g:ℝ→ℝ)(physical:Coupling G g)(h q P A:ℕ)(reserve:P<A)(order:P+A*(2*h+1)<q+1)
    (u:Scan G n)(v:Scan G 1)(K:Set (Points n))(closed:IsCompact K)(inside:K⊆conf n)(φ:Test 2):
    ∀ᶠ r in trail,∀ψ:Test n,tsupport ψ⊆K →
      ‖ordinary Z q (g r) (age A (g r)) u v ψ φ-
        ∑b:Dframe.Toon G h,cutoff q (g r) (converted Z M ν u ψ (Dframe.flash b))*
          two Z q (g r) (age A (g r)) v b φ‖≤Read.Value ψ*Read.Value φ*(g r)^(P+A*(2*h+1)):=by
  have source:=(ms.separatedOPE ν).wilson
  obtain ⟨δ,positive,safe⟩:=clearance K closed inside φ
  have pos:0<A:=by omega
  have narrow:Tendsto (fun r=>((g r)^A)^2) trail (𝓝 0):=by
    simpa [zero_pow pos.ne'] using ((physical.conforms simple).pow A).pow 2
  filter_upwards [narrow.eventually (ge_mem_nhds positive),
    WilsonPublicForkIndependentPlacement.reflected Z M ν ms g physical h q P A reserve order u v K closed inside φ,
    physical.positive] with r room bill gp ψ mem
  let s:=age A (g r)
  let T:=fee s (-(totalG v:ℝ))
  let f:=fun p:Points n×Points 2=>T*cutoff q (g r) (joint Z u v p.1 (relative p.2) s)
  let a:=fun (b:Dframe.Toon G h) x=>cutoff q (g r) (front Z u b x)
  let l:=fun (b:Dframe.Toon G h) z=>T*cutoff q (g r) (leg Z v b (relative z) s)
  have ⟨temp,scale⟩:=same_clock pos gp
  have space_r:(1:ℝ)/Real.exp s≤δ:=by rw [one_div,scale,inv_inv];exact room
  have placed_eq(x:Points n)(z:Points 2):
      forest x (squeeze (-s) (relative z))=placed 1 (Real.exp s) x (relative z):=by
    ext1 i;induction i using Fin.addCases <;> simp [placed,squeeze]
  have fit(p:Points n×Points 2)(hp:p∈space ψ φ):forest p.1 (squeeze (-s) (relative p.2))∈conf (n+1):=by
    rw [placed_eq];exact safe 1 (Real.exp s) zero_lt_one (Real.exp_pos s) space_r _ (mem hp.1) _ hp.2
  have shifted:Continuous (fun z:Points 2=>squeeze (-s) (relative z)):=
    (continuous_const_smul _).comp continuous_relative
  have fC:ContinuousOn f (space ψ φ):=by
    apply continuousOn_const.mul;apply continuous_cut;intro k _
    exact (source.awake _ _ k).comp (continual continuous_fst (shifted.comp continuous_snd)).continuousOn fit
  have aC(b:Dframe.Toon G h):ContinuousOn (a b) (tsupport ψ):=by
    apply continuous_cut;intro k _;exact ((source.far u).2.1 _ k).mono ψ.tsupport_subset
  have lC(b:Dframe.Toon G h):ContinuousOn (l b) (tsupport φ):=by
    apply continuousOn_const.mul;apply continuous_cut;intro k _
    apply (source.awake _ _ k).comp (continual continuous_const shifted).continuousOn
    intro z hz;exact lives (-s) (WilsonPublicForkIndependentPlacement.outside φ ⟨z,hz,rfl⟩)
  have rewrite(b:Dframe.Toon G h):ψ.applyTo (a b)=cutoff q (g r) (converted Z M ν u ψ (Dframe.flash b)):=
    converted_profile Z M ν ms q (g r) u ψ b
  change ‖tested ψ φ f-∑b,cutoff q (g r) (converted Z M ν u ψ (Dframe.flash b))*φ.applyTo (l b)‖≤_
  simp_rw [←rewrite]
  rw [cut ψ φ f a l fC aC lC]
  apply mass
  rintro p ⟨px,pz⟩
  have cap:=bill _ (mem px) _ pz
  unfold contrast at cap;rw [temp] at cap
  change ‖T*cutoff q (g r) (joint Z u v p.1 (relative p.2) s)-
    ∑b:Dframe.Toon G h,a b p.1*(T*cutoff q (g r) (leg Z v b (relative p.2) s))‖≤_
  convert cap using 2
  dsimp only [a];rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl;intro b _;ring

end YM.Integration.WilsonPublicForkIndependentHearing
