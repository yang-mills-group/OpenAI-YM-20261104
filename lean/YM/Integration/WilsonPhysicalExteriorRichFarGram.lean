import YM.Integration.WilsonPhysicalExteriorRichFarDeposit

/-! The matrix of the full, actual finite R-rich closed field readings, on the
one smooth far detector presold by its independent physical tree Gram. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarGram
open Function Filter Set Finset Real MeasureTheory Metric Lattice RG RG16 Pert Pert.Position
open XSpace XSpace.Cirrus XSpace.Structure1 FVA2 FVA2.Register MS MS.Land MS.Menus MS.Rake MS.Tone
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorQuadratureClock WilsonPhysicalExteriorFirstCutScale
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorRichFarCells Extra.FD
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (Q:Prescription (Press.portDeck G)) (H:ℕ)
local notation "B₀" => Press.portDeck G
local notation "I" => Glyph B₀ H
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

def gram (g:Test 2) (c c':ℝ) (side:Bool) (u:ℝ) (k j per:ℕ) : Matrix I I ℂ:=fun a b=>
  WilsonPhysicalExteriorRichFarDeposit.reading R Q (WilsonPhysicalExteriorFormalGram.word H a b)
    g c c' side u k j per

private theorem scales (hG:G.Simple) (μ:ℝ)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c':ℝ} (hc':1<c') :
    ∀ᶠ j:ℕ in atTop,1+|μ+log (T₀ c' j)|≤exp (3*Λ j) ∧
      1+|(μ+R.family.S.scale j)+log (T₀ c' j)|≤exp (3*Λ j) := by
  have e:=tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)
  filter_upwards [shift R hG μ,shift R hG 0,e.eventually_ge_atTop (1+|μ|),e.eventually_ge_atTop 2,
    (WilsonPhysicalExteriorCompactWindow.recedes R hG slow hc').eventually_ge_atTop 1] with j h₁ h₂ hab hg hT
  change 1+|μ|≤exp (Λ j) at hab
  change (2:ℝ)≤exp (Λ j) at hg
  have times (i:ℕ):0≤R.family.S.scale i:=by
    simpa only [R.family.S.scale_zero] using (OPE.scale_mono R.family.S).monotone (Nat.zero_le i)
  have hy:0≤log (T₀ c' j):=log_nonneg hT
  have cap:log (T₀ c' j)≤R.family.S.scale j:=by
    rw [WilsonPhysicalExteriorFirstCutScale.ratio,log_exp]
    exact sub_le_self _ (times _)
  have clock:R.family.S.scale j≤exp (2*Λ j):=by
    simp only [zero_add,abs_of_nonneg (times j)] at h₂;linarith
  have grow:exp (Λ j)≤exp (2*Λ j):=by exact exp_le_exp.mpr (by linarith only [Literal.lambda_pos R.family j])
  have full:exp (2*Λ j)+exp (2*Λ j)≤exp (3*Λ j):=by
    rw [show (3:ℝ)*Λ j=2*Λ j+Λ j by ring,exp_add]
    nlinarith only [mul_le_mul_of_nonneg_left hg (exp_pos (2*Λ j)).le]
  constructor
  · exact (by linarith only [abs_add_le μ (log (T₀ c' j)),abs_of_nonneg hy,
      hab.trans grow,cap.trans clock] : 1+|μ+log (T₀ c' j)|≤exp (2*Λ j)+exp (2*Λ j)).trans full
  · exact (by linarith only [abs_add_le (μ+R.family.S.scale j) (log (T₀ c' j)),abs_of_nonneg hy,
      h₁,cap.trans clock] : 1+|(μ+R.family.S.scale j)+log (T₀ c' j)|≤exp (2*Λ j)+exp (2*Λ j)).trans full

private theorem aperture (g:Test 2) (pop:Nonempty (tsupport g)) :
    ∃A δ:ℝ,0<A ∧ 0<δ ∧ (∀z∈tsupport g,∀i,‖relative z i‖≤A) ∧
      ∀z∈tsupport g,∀i l:Fin 2,i≠l→δ≤‖Fountain.metric z i-Fountain.metric z l‖ := by
  have co(i:Fin 2):Continuous (fun x:Points 2=>Fountain.metric x i):=
    Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2=>E4)).continuous)
  let f(x:Points 2):=Fountain.metric x 1-Fountain.metric x 0
  have continuous:Continuous f:=(co 1).sub (co 0)
  obtain ⟨A,mark⟩:=g.hasCompactSupport.exists_bound_of_continuousOn continuous.continuousOn
  obtain ⟨r,hr,lowest⟩:=g.hasCompactSupport.exists_isMinOn (Set.nonempty_coe_sort.mp pop) continuous.norm.continuousOn
  have pos:0<‖f r‖:=norm_pos_iff.mpr (sub_ne_zero.mpr ((Fountain.metric_conf (g.tsupport_subset hr)).ne (by decide)))
  refine ⟨max 1 A,‖f r‖,zero_lt_one.trans_le (le_max_left ..),pos,?_,?_⟩
  · intro z hz i;fin_cases i
    · change ‖Fountain.metric z 0-Fountain.metric z 0‖ ≤ max 1 A
      rw [sub_self,norm_zero];exact (zero_le_one: (0:ℝ)≤1).trans (le_max_left 1 A)
    · exact (mark z hz).trans (le_max_right ..)
  · intro z hz i l ne;fin_cases i <;> fin_cases l
    · exact (ne rfl).elim
    · change ‖f r‖≤‖Fountain.metric z 0-Fountain.metric z 1‖
      rw [norm_sub_rev (Fountain.metric z 0) (Fountain.metric z 1)];exact lowest hz
    · exact lowest hz
    · exact (ne rfl).elim

/-- Before every regulator: all named pairs and both physical subtraction
clocks, at every prescribed order. The right hand side is the unrounded
independent compact detector, with its exact time change. -/
theorem measured {hG:G.Simple} (N:WilsonPrescription G) {S:Prescription B₀} {dial:Bool}
    (issued:Main.Match N hG M S dial) (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (g:Test 2) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) (pop:Nonempty (tsupport g))
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀s:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀a b:I,
      let err:=fun u:ℝ=>(T₀ c' j)^h*
        ‖gram R Q H g c c' s u k j per a b-MSSeparatedTestGram.matrix M H (u+log (T₀ c' j)) k g a b‖
      err μ≤exp (-q*Λ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ j) := by
  obtain ⟨A,δ,ha,hd,size,split⟩:=aperture g pop
  obtain ⟨B,hB,fee⟩:=TestBudget.bound_fin g
  have current:=Filter.eventually_all.mpr (fun a:I=>Filter.eventually_all.mpr fun b:I=>
    WilsonPhysicalExteriorRichFarDeposit.measured R M Q (hG:=hG) rows (WilsonPhysicalExteriorFormalGram.word H a b)
    g good (tsupport g) pop g.tsupport_subset Subset.rfl ha hd size split slow h₁ h₂ h₃ lo μ (q+1) k h)
  have historic:=WilsonPhysicalExteriorSampledGram.whole R M H N issued k (tsupport g) g.hasCompactSupport
    g.tsupport_subset slow h₁ h₂ h₃ lo h 3 (q+1)
  have grow:∀ᶠ j:ℕ in atTop,B+1≤exp (Λ j):=(tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)).eventually_ge_atTop (B+1)
  filter_upwards [current,historic,grow,scales R hG μ slow h₁] with j hj ho big logs s per hp a b
  have part:=hj a b s per hp
  let T:=T₀ c' j
  let m:=grid R c c' true s (j,per)
  let E:=exp (-(q+1)*Λ j)
  let cost (ν:ℝ):=T^h*‖gram R Q H g c c' s ν k j per a b-
    WilsonPhysicalExteriorSampledGram.matrixOn M H m g (ν+log T) k a b‖
  have sumPrice (ν:ℝ) (legal:1+|ν+log T|≤exp (3*Λ j)) (bound:cost ν≤E) :
      T^h*‖gram R Q H g c c' s ν k j per a b-MSSeparatedTestGram.matrix M H (ν+log T) k g a b‖≤exp (-q*Λ j):=by
    let Z:=WilsonPhysicalExteriorSampledGram.matrixOn M H m g (ν+log T) k a b
    let X:=gram R Q H g c c' s ν k j per a b
    let W:=MSSeparatedTestGram.matrix M H (ν+log T) k g a b
    have next:=ho true s per hp g Subset.rfl B fee (ν+log T) legal a b
    change T^h*‖Z-W‖≤B*E at next
    change T^h*‖X-Z‖≤E at bound
    change T^h*‖X-W‖≤_
    calc
      _≤T^h*(‖X-Z‖+‖Z-W‖):=mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using dist_triangle X Z W)
          (pow_nonneg (show 0<T from exp_pos _).le _)
      _≤(B+1)*E:=by rw [mul_add];linarith only [bound,next]
      _≤exp (Λ j)*E:=mul_le_mul_of_nonneg_right big (exp_pos _).le
      _=exp (-q*Λ j):=by dsimp only [E];rw [←Real.exp_add];congr 1;ring
  exact ⟨sumPrice μ logs.1 part.1,sumPrice (μ+R.family.S.scale j) logs.2 part.2⟩

end YM.Integration.WilsonPhysicalExteriorRichFarGram
end
