import YM.Juniper.Bright.Capital
/-!
 # Arbitrary power at going scale of now!! weighted E6 headed atoms (pre-ρ)

 Uniform at all periods c on the patch (few supports needed to pay Price.L).
 Deliver Cut receipts. Expose outcome estimates `Hit`, each old ν. Actual deployment in Volte.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
      {W μ x C A v r a s q B d M i γ:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R}
      {j n k b: ℕ}

lemma cloud (Q: ConnectedActivityE6.Target G P) (L:Side) (n:ℕ) {μ:ℝ} (hμ:0<μ): ∀ᶠ s:ℝ in atTop, let u:=grow G L s ^ n
       u≤ Real.exp (Q.mark L μ s) ∧ u ≤ Real.exp (Q.ε*(Pressure.Stores.till s/(L.val:ℝ))):= by
    let d:= grow G L; let v:= -(3/8:ℝ)*n-1
    let p(s:ℝ):=Q.ε*(Pressure.Stores.till s/(L.val:ℝ))
    have hy : Rate G L v (fun x=> Real.exp (-p x)) := by
      have hp:= Rate.cutoff (a:=v) (G:=G) (L:=L) (δ:=Q.ε/L.val) (div_pos Q.usable (by positivity)); refine hp.congr (Eventually.of_forall fun i=>?_)
      beta_reduce; congr 1; unfold p; ring
    have he : Rate G L v (fun x=> Real.exp (-(Q.mark L μ x))) := by
      apply (Rate.monitor_cutoff (show 0<μ/4 by positivity) (show (0:ℝ)<2 by norm_num)).congr
      refine Eventually.of_forall fun x=> ?_; dsimp only; rw [Real.rpow_two]; change Real.exp (-Delay.hatWin G L _ _ x) = _ -- which side? from probed
      unfold Delay.hatWin; congr 1; ring
    have hg:= (Rate.power (G:=G) (L:=L) (a:=3/8)).pow n
    have hv:3/8*(n:ℝ)+v<0:= by unfold v; ring_nf; norm_num
    filter_upwards [(hg.mul he).below hv 1 zero_lt_one,(hg.mul hy).below hv 1 zero_lt_one] with x hx hh u
    have H (z:ℝ) (hz:|u*Real.exp (-z)|≤1): u ≤ Real.exp z:= (div_le_one (Real.exp_pos _)).mp (by rw [div_eq_mul_inv,←Real.exp_neg]; exact (le_abs_self _).trans hz)
    exact ⟨H _ hx,H _ hh⟩

-- Precision.Wanted advertised all powers at actual β before Delay buy.
abbrev Valuable (e:Q.Expense)(L:Side)(n x:ℕ)(t:ℕ)(χ: Chi)(B a:ℝ)(p: ℝ)(o: Target.Order G W): Prop := ∀ (c' f:Side)(S:StepData c' f)(T:Tube G S), Works P L B S T→ Stamp T→ ∀ (R:Rep G f)(Z:ℝ)(H:Cash W B a L Q o Z T R),
    ∃ (l:ℕ) (β θ M s v u i r y z:ℝ) (N: Captain H t β θ s v u M r y z l χ), Armada Q L a e.earn B i y t l ∧
       Ac.Hit (Captain.reachability (H:=H)) (radiusB B) (fun z=> if high H n z then N.markΦ z x else 0) e.earn (betaF G B L^p) ∧
       collars G i B t x*(salary Q L a y B t l*(1-1/2)⁻¹) ≤ betaF G B L ^e.wanting
namespace Armada
-- one fixed δ axis bound independent of period; pay δ through world owner
private lemma poised (h : Armada Q L μ a x i B j k) : 0 ≤ i := h.delta.le
end Armada
lemma pearl (Q: ConnectedActivityE6.Target G P):∃ m:ℕ, ∀ L:Side,m≤L.val→ ∀ (X:Q.Expense)(W μ:ℝ)(o:Target.Order G W),0<W→0<μ→X.wanting< -(3/8:ℝ)→
       ∀ (p:ℝ) (k n j:ℕ), (-(3/8:ℝ))*k<p → ∀ (χ:Chi), ∀ᶠ B:ℝ in atTop, Valuable X L k n j χ B μ p o:=by
  obtain ⟨m,hm⟩:= Bright.assemble P Q; refine ⟨m,fun L hL X W μ o hW hμ hV p k n j hK χ=>?_⟩
  by_cases he : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · exact Eventually.of_forall fun x c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim
  obtain ⟨D,hd,hF,hX⟩:= he; obtain ⟨A,a,C,d,v,t,r,B,q,l,hB,H⟩:= hm L hL D hd k j χ W hW μ hμ o
  obtain ⟨y,hg,hT⟩:= Armada.ensemble Q L hμ X.earn X.price (by linarith [X.worth,X.first,X.second]) j l hB
  have hy:0<y:= by obtain ⟨x,hx⟩:= hT.exists; exact hx.delta
  have hs:Rate G L Q.rate (fun x=>salary Q L μ (B x) x j l) := by
    let h := ((Rate.const 1).add (hB.mul_left (2^j:ℝ))).mul (Q.rate_none L hμ 0 l 0); rw [zero_add] at h; exact h
  let f(x):=(grow G L x^k)⁻¹; let g(x):= grow G L x * (collars G y x j n * (salary Q L μ (B x) x j l*(1-1/2)⁻¹))
  have hf : Rate G L (-(3/8:ℝ)*k) f:= by
    apply Rate.congr Rate.power
    filter_upwards [Delay.shift_pos G L] with x hx; unfold f grow
    rw [neg_mul,Real.rpow_neg hx.le, Real.rpow_mul hx.le]; simp
  have hh : Q.rate < -(3/8:ℝ):= X.reach.trans hV
  have ht: Rate G L (3/8+Q.rate) g:= by unfold g; apply (Rate.power (G:=G) (L:=L) (a:=3/8)).mul; simpa only [pow_zero,mul_one] using hg n 0
  have ha := (hf.mul ht) p (by linarith only [hh,hK]); have hK := (hg n 0) X.wanting X.reach
  filter_upwards [ha,H,hT, Height.pressureYoung G L (i:=Q.δ) (Q.rate_root L hμ (β:=1) (C:=0)) (by linarith only [hh]), Height.pressureYoung G L (i:=y) hs (by linarith only [hh]), cloud Q L k hμ,(Work.E09.betaF_growth G L).eventually_ge_atTop 1,hK] with
      x hx h hT h₁ h₂ hΩ ht hσ c f' S T hG Hp R s I
  obtain ⟨Ξ,hΞ⟩:= h _ _ S T (hG.patch hF hX) Hp R s I
  simp only [pow_zero,mul_one] at hσ
  refine ⟨l,C,d x,a,v x,t x,A,y,r x,B x,q x,Ξ,hT,?_,(le_abs_self _).trans hσ⟩ -- order Vars Value
  intro z; refine budget_loosen (fortune Ξ (Real.one_le_rpow ht (by norm_num)) hΞ hT h₁ h₂ hΩ.1 hΩ.2 n z) ((?_ : _ = f x*g x).trans_le ((le_abs_self _).trans hx))
  unfold f g; ring
end YM.Juniper.Bright
