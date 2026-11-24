import YM.Integration.FVA1Physical.Wilson.NormalizedRows

/-! Buy the full uncut covariance and full normalized outgoing polynomial
row before the volume, root, forest or detailed source are selected. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G:Gauge}

theorem full_covariance_rows (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (simple:G.Simple) (H H':Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G) (s:ℕ) :
    ∃ C:ℝ, ∀ᶠ x:ℝ in atTop, ∀ (A:Mosaic.Issue G) (_b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      LoopNet (address A.F G) (αm (tip G P.L x)) s (fullCov A) C := by
  obtain ⟨v,buy⟩:=purchased_chart_chance J clear simple H H' P K branch (D:=0) le_rfl 0
  by_cases ok:0 < v.gap ∧ 0 < v.a ∧ 0 < v.density
  swap
  · refine ⟨0,?_⟩
    filter_upwards [buy] with x grant
    intro A b patch kernel season
    have paid:=(grant A patch kernel season 0 b (by simp)).1.buys
    exact False.elim (ok ⟨paid.pos_m,paid.pos_a,paid.pos_C⟩)
  obtain ⟨C,W,seats⟩:=waiting v H H' J χ hχ clear P 3 s
  let X:=fun x:ℝ=>tip G P.L x
  have rise:Tendsto X atTop atTop:=Work.E09.betaF_growth G P.L
  have fr:0 < frond v.coords v.density v.gap v.a:=div_pos
    (tiltWidth_pos _ ok.1 ok.2.1 ok.2.2.le) (by norm_num)
  have slow:Tendsto (fun x=>αm (X x)) atTop (𝓝 0):=by
    have h:=(Mosaic.Issue.thorn_top rise 0).mul_const 10
    simpa [Mosaic.Issue.thorn] using h
  refine ⟨C,?_⟩
  filter_upwards [buy,seats,slow.eventually (gt_mem_nhds fr)] with x grant theater small
  intro A b patch kernel season
  let y:=X x
  obtain ⟨paid,cal,_,_⟩:=grant A patch kernel season 0 b (by simp)
  obtain ⟨solver,_⟩:=theater.enter _ _ patch season (boxX y b) (boxY y b) A.F 0 A.v paid
    (by rw [patch]; exact cal.first)
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry; positivity
  let r:=αm y/2
  have r0:0 ≤ r:=div_nonneg a0 (by norm_num)
  have sol:=solver r r0 (by dsimp [r,y]; linarith)
  have gain:=Spruce.pitches A.F A.pre A.v (boxX y b) b sol r0 r0 (Mosaic.housing A.F b y)
  have eqn:r+r=αm y:=by dsimp only [r]; ring
  exact eqn ▸ gain.full

theorem purchased_normalized_rows (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ)
    (simple:G.Simple) (H H':Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G)
    (p m h s:ℕ) (hm:1 ≤ m) {η:ℝ} (hη:0 < η) :
    ∃ δ:ℝ, 0 < δ ∧ ∀ᶠ x:ℝ in atTop, ∀ (A:Mosaic.Issue G) (b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      let d:=p+1+p
      Kind A.T → Expanse A.T 1 d → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s d →
      ∀ src:PowerSeries (Pot (Joint A.F G)),
        (∀ i ≤ d,Vault (address A.F G) {b} (αm y) s (h+2*Whisk.ribbon m d+1) 0 (PowerSeries.coeff i src) (y^δ) ∧
          (PowerSeries.coeff i src).totalDegree ≤ m) →
        ∀ i ≤ p,Vault (address A.F G) {b} (αm y) s h 0 (PowerSeries.coeff i (normalizedRows A χ src p)) (y^η) := by
  let d:=p+1+p
  obtain ⟨δ,hδ,toll⟩:=row_exponent m d h hη
  obtain ⟨C,law⟩:=full_covariance_rows J clear χ hχ simple H H' P K branch s
  have rise:=Work.E09.betaF_growth G P.L
  refine ⟨δ,hδ,?_⟩
  filter_upwards [law,distributed_action J χ hχ simple H H' P K d s (h+2*Whisk.ribbon m d) hδ,
    rise.eventually (toll C)] with x cover distributed price
  intro A b patch kernel season y d' kind plane budget src input i hi
  obtain ⟨kind',full⟩:=distributed A patch kernel season kind plane budget
  have a0:0 ≤ αm y:=by unfold αm hatW Alto.flurry; positivity
  have he : Expanse (barbed A.F A.v χ A.T) m d:=by
    constructor
    intro j hj
    have enough : j ≤ m*j:= le_mul_of_one_le_left (Nat.zero_le j) hm
    exact (full j hj).2.trans (by omega)
  have V:=normalized_jet b p m h s a0 (cover A b patch kernel season) (barbed A.F A.v χ A.T) src kind' he
    (fun j hj=>(full j hj).1) input hi
  exact Quote.widen V price le_rfl

end YM.Integration.FVA1Physical.Wilson
