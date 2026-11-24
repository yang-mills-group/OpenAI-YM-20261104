import YM.Integration.ActualRunSpring
import YM.Integration.ConditionalAffineForcing
import YM.Integration.ConditionalAffineLocalizedProduct
import YM.Integration.ConditionalCovarianceRoots

/-! Actual all-position affine source price on a funded no-hole aperture.
The signed plaquettes, face transport and noise transport retain their
own physical path entries, independent data and original cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineSourcePrices
open Filter Set Function Lattice Wilson RG Precision Exterior Tree Matrix Pressure Pressure.Tube Pressure.Stores
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset ProjectorNext.Equivariance
open FreeResolvent FreeResolvent.TestD Push.Uniform ConditionalAffineRetainedEndpoints ConditionalAffineCoarsePlaquettes
open ConditionalAffineNoiseCoordinates ConditionalAffineLocalizedProduct
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

def root (S : StepData c f) (i : Slots S) : Site c := i.1.act (i.2.elim (fun h : Twin f => S.ratio.parent h.1.1) (fun h : Bond c => h.1))

def fineTail (T : Tube G S) (s : Signed) (R : ℕ) (i : Twin f) (B : PriceCoords G c) : G.Color :=
  let U := FreeResolvent.Affine.shone S s ((arrange G c).symm B)
  PhysicalAffineScalarUncut.plaquetteRows T.up T.high U i - T.Xf R U i

private theorem transport_field (B : PriceCoords G c) : represent (FreeResolvent.Affine.decode ((arrange G c).symm B))=AnalyticBridge.SectorAffine.field 1 B := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using (field G c ((arrange G c).symm B)).symm

theorem flat_field (s : Signed) : Tendsto (turn s (1:Config G c)) (𝓝 0) (𝓝 1) := by
  have hf : Continuous (fun B : PriceCoords G c => AnalyticBridge.SectorAffine.field (1:Config G c) B) := by
    apply continuous_pi
    intro i
    change Continuous (fun B => G.lieExp ((gaugeCount (G:=G) (ι:=Bond c)) B i) * (1:Config G c) i)
    fun_prop
  have h : ContinuousAt (turn s (1:Config G c)) (0:PriceCoords G c) := by
    change ContinuousAt (fun B : PriceCoords G c => pull s 0 (AnalyticBridge.SectorAffine.field (1:Config G c) B)) 0
    exact (continuous_pull (G:=G) s 0).continuousAt.comp hf.continuousAt
  simpa only [ConditionalAffineCoarsePlaquettes.turn_flat] using h.tendsto

private theorem germ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : Site c} {δ M : ℝ} {n : ℕ}
    {F H : PriceCoords G c→E} (h : F =ᶠ[𝓝 0] H) (hH : Point 0 p δ n H M) : Point 0 p δ n F M := by
  exact hH.germ h.symm

/-- The discarded fully transported fine plaquette is charged at the
physical signed parent in the old stage's coarse coordinate system. -/
theorem fine (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) : ∃ δ K : ℝ, 0<δ ∧ 0<K ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (_F : Forest S.ratio) (s : Signed)
    (R : ℕ) (i : Twin f), Point 0 (s.act (S.ratio.parent i.1.1)) δ n (fineTail T s R i) (K*Real.exp (-(P.top.width/2)*R)) := by
  obtain ⟨Z,hZ⟩ := paint_supply G n
  let δ := entryWidth n L (P.top.width/2)
  let W := rootsCost G Z (P.top.width/2) n
  let K := 1+Real.exp (δ*n)*P.top.paths*|W|
  have hδ : 0<δ := width_positive (half_pos P.top.width_pos) n L
  have hK : 0<K := by unfold K; have h:=P.top.paths_pos; positivity
  refine ⟨δ,K,hδ,hK,?_⟩
  intro c f S T hP hL F s R i
  obtain ⟨a,b,ha,hb⟩ := hP.feeds
  rcases i with ⟨i,q⟩
  cases q
  · have hz : fineTail T s R (i,false) = 0 := by
      funext B
      change PhysicalAffineScalarUncut.plaquetteRows T.up T.high _ (i,false)-T.Xf R _ (i,false)=0
      exact sub_self _
    rw [hz]
    exact Point.zero (mul_nonneg hK.le (Real.exp_pos _).le)
  let Y := fun B => T.up.ell (FreeResolvent.Affine.shone S s B) i-shorten T.up R 1 (FreeResolvent.Affine.shone S s B) i
  let U := fineTail T s R (i,true)
  have eq : Y = U ∘ arrange G c := by ext z; simp [Y,U,fineTail,PhysicalAffineScalarUncut.plaquetteRows,Tube.Xf,plotted]
  have hL' : S.ratio.count=L := hL
  have hr : S.ratio.parent (affine s 0 i.1)=s.act (S.ratio.parent i.1) := by simp [affine,S.ratio.parent_signed S.patch.odd_side]
  have hc := ConditionalAffinePlaquetteJets.smooth_raw F s T.up i R 1 n (by decide) ha
  have hv : ContDiffAt ℝ n U 0 := by
    have h₀ : ContDiffAt ℝ n Y ((arrange G c).symm (0 : PriceCoords G c)) := by
      simpa only [Y,map_zero] using hc
    have h : ContDiffAt ℝ n (Y ∘ (arrange G c).symm) (0 : PriceCoords G c) :=
      h₀.comp _ (arrange G c).symm.contDiff.contDiffAt
    have he : Y ∘ (arrange G c).symm = U := by
      funext B
      change Y ((arrange G c).symm B) = U B
      rw [eq,Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
    exact he ▸ h
  refine ⟨hv,fun l hl => ?_⟩
  let x := index G c ∘ l.get
  have h := ConditionalAffinePlaquetteJets.price F s T.up i R 1 n (by decide) ha hZ hl x
  have h₁ : Real.exp (δ*Stars.rays (native c) (s.act (S.ratio.parent i.1)) (FreeResolvent.Affine.hearth∘x))=
      (marks G c δ).pay l (s.act (S.ratio.parent i.1)) := by
    rw [←Stars.pays,read_pay]
  have h₂ : iteratedFDeriv ℝ l.length Y 0 (FreeResolvent.Affine.ray G c∘x)=jet bolt U l 0 := by
    rw [eq,←Stars.list_result,read_jet]
  change _ * ‖iteratedFDeriv ℝ l.length Y 0 (FreeResolvent.Affine.ray G c∘x)‖≤_ at h
  rw [hL',hr,h₂,h₁] at h
  apply h.trans
  simp only [Nat.cast_one,div_one]
  have ht := (Real.exp_pos (-(P.top.width/2)*(R:ℝ))).le
  have ha0 := roots_nn hZ (half_pos P.top.width_pos)
  have hlen : Real.exp (δ*l.length)≤Real.exp (δ*n) := Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hδ.le)
  have hmany := mul_le_mul_of_nonneg_right hlen (mul_nonneg P.top.paths_pos.le (show 0≤W from ha0))
  have hcost : Real.exp (δ*l.length)*(P.top.paths*W)≤K := hmany.trans (by unfold K W; rw [abs_of_nonneg ha0]; nlinarith)
  simpa only [W,mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_right hcost ht

/-- A single strictly positive truncation rate purchased by the four
actual original contributions to the affine error. -/
def rate (P : Teller G) (L : Side) := min (P.top.width/2)
  (min (P.below.width/(2*(L.val:ℝ))) (min (P.η/(10*(L.val:ℝ))) (P.η/(2*(L.val:ℝ)))))

theorem rate_pos (P : Teller G) (L : Side) : 0<rate P L := by
  unfold rate
  have hx : (0:ℝ)<L.val := by exact_mod_cast L.property
  exact lt_min (half_pos P.top.width_pos) (lt_min (div_pos P.below.width_pos (by positivity))
    (lt_min (div_pos P.width (by positivity)) (div_pos P.width (by positivity))))

/-- The complete original aperture/source discrepancy, through every
independent coarse derivative, in the same physical signed row. -/
theorem total (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) : ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ 0<rate P L ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (_F : Forest S.ratio)
    (x : ℝ), 0<temp x → ∀ i : Slots S, Point 0 (root S i) δ n
      (fun B => ConditionalAffineSourceSplit.difference T x ((arrange G c).symm B) i)
      (M*Real.exp (-rate P L*(till x:ℝ))) := by
  obtain ⟨a,A,ha,hA,hf⟩ := fine G P L n
  obtain ⟨b,B,hb,hB,hm⟩ := carried_endpoint G P L n
  obtain ⟨d,D,hd,hD,hw⟩ := ConditionalAffineLocalizedProduct.face G P L n
  obtain ⟨e,E,he,hE,hn⟩ := ConditionalAffineLocalizedProduct.noise G P L n
  let δ := min a (min b (min d e))
  have hδ : 0<δ := lt_min ha (lt_min hb (lt_min hd he))
  let M := A+B+D+E
  have hM : 0<M := by unfold M; linarith
  refine ⟨δ,M,hδ,hM,rate_pos P L,?_⟩
  intro c f S T hP hL F x hx i
  let R := till x
  let τ := Real.exp (-rate P L*(R:ℝ))
  have hyp (j : ℝ) (hj : rate P L≤j) : Real.exp (-j*(R:ℝ))≤τ := Real.exp_monotone
    (mul_le_mul_of_nonneg_right (neg_le_neg hj) (Nat.cast_nonneg R))
  have hL0 : (0:ℝ)<L.val := by exact_mod_cast L.property
  have htop : Real.exp (-(P.top.width/2)*(R:ℝ))≤τ := hyp _ (min_le_left ..)
  have rateBorn : rate P L≤P.below.width/(2*(L.val:ℝ)) := (min_le_right ..).trans (min_le_left ..)
  have rateWide : rate P L≤P.η/(10*(L.val:ℝ)) := (min_le_right ..).trans ((min_le_right ..).trans (min_le_left ..))
  have rateNoise : rate P L≤P.η/(2*(L.val:ℝ)) := (min_le_right ..).trans ((min_le_right ..).trans (min_le_right ..))
  have hl : Real.exp (-(P.below.width/2)*((R:ℝ)/L.val))≤τ := by convert hyp _ rateBorn using 2; ring
  have hf' : Real.exp (-(P.η/2)*((R:ℝ)/(5*(L.val:ℝ))))≤τ := by convert hyp _ rateWide using 2; ring
  have hn' : Real.exp (-(P.η/2)*((R:ℝ)/L.val))≤τ := by convert hyp _ rateNoise using 2; ring
  have hτ : 0≤τ := (Real.exp_pos _).le
  have hδa : δ≤a := min_le_left _ _
  have hδb : δ≤b := (min_le_right a (min b (min d e))).trans (min_le_left b (min d e))
  have hδd : δ≤d := (min_le_right a (min b (min d e))).trans
    ((min_le_right b (min d e)).trans (min_le_left d e))
  have hδe : δ≤e := (min_le_right a (min b (min d e))).trans
    ((min_le_right b (min d e)).trans (min_le_right d e))
  rcases i with ⟨s,j|j⟩
  · have a₀ := (hf S T hP hL F s R j).mono hδa (mul_le_mul_of_nonneg_left htop hA.le)
    have b₀ := ((hm S T hP hL s R).1 j).mono hδb (mul_le_mul_of_nonneg_left hl hB.le)
    have d₀ := (hw S T hP hL s R j).mono hδd
      (mul_le_mul_of_nonneg_left hf' hD.le)
    have h := (a₀.sub d₀).sub b₀
    apply germ (H:=fun z => fineTail T s R j z - Pressure.zip
      (fun i l => PhysicalAffineScalarUncut.faceStack T (turn s 1 z) i l-T.Φ R (turn s 1 z) i l)
      (fun l => value T s l z) j - Pressure.zip (T.Φ R (turn s 1 z)) (fun l => endpoint T s R l z) j) _
      (h.mono le_rfl (by unfold M; nlinarith only [mul_nonneg hE.le hτ]))
    filter_upwards [ConditionalAffineSourceSplit.healthy_germ T R hx (flat_field s)] with B hB
    simp only [ConditionalAffineSourceSplit.difference,Sum.elim_inl,transport_field]
    change _ - _ - _ - Pressure.zip _ (_-T.vision R (temp x) (turn s 1 B)) j = _
    rw [hB]; rfl
  have b₀ := ((hm S T hP hL s R).2 j).mono hδb (mul_le_mul_of_nonneg_left hl hB.le)
  have e₀ := (hn S T hP hL s R j).mono hδe
    (mul_le_mul_of_nonneg_left hn' hE.le)
  have h := e₀.neg.sub b₀
  apply germ (H:=fun z => -Pressure.zip
    (fun i l => PhysicalAffineScalarUncut.noiseStack T (turn s 1 z) i l-T.Φ' R (turn s 1 z) i l)
    (fun l => value T s l z) j - Pressure.zip (T.Φ' R (turn s 1 z)) (fun l => endpoint T s R l z) j) _
    (h.mono le_rfl (by unfold M; nlinarith only [mul_nonneg hA.le hτ,mul_nonneg hD.le hτ]))
  filter_upwards [ConditionalAffineSourceSplit.healthy_germ T R hx (flat_field s)] with B hB
  simp only [ConditionalAffineSourceSplit.difference,Sum.elim_inr,transport_field]
  change -_ - Pressure.zip _ (_-T.vision R (temp x) (turn s 1 B)) j = _
  rw [hB]; rfl

/-- The same nonlinear source bound in the original raw independent log
coordinates used by the actual conditional Hessian and scalar. -/
theorem raw (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) : ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ 0<rate P L ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (_F : Forest S.ratio)
    (x : ℝ), 0<temp x → ∀ (i : Slots S) (k : ℕ), k≤n → ∀ l : Fin k→FreeResolvent.Affine.raw G c,
      Real.exp (δ*Stars.rays (native c) (root S i) (FreeResolvent.Affine.hearth∘l))*
      ‖iteratedFDeriv ℝ k (fun B => ConditionalAffineSourceSplit.difference T x B i)
        0 (FreeResolvent.Affine.ray G c∘l)‖≤M*Real.exp (-rate P L*(till x:ℝ)) := by
  obtain ⟨δ,M,hδ,hM,hρ,H⟩ := total G P L n
  refine ⟨δ,M,hδ,hM,hρ,?_⟩
  intro c f S T hP hL F x hx i k hk l
  let U := fun B => ConditionalAffineSourceSplit.difference T x ((arrange G c).symm B) i
  have H' := (H S T hP hL F x hx i).bound (List.ofFn ((index G c).symm∘l)) (by simpa using hk)
  have h : (fun B => ConditionalAffineSourceSplit.difference T x B i)=U∘arrange G c := by ext B; simp [U]
  rw [h,directions]
  rw [Stars.pays,Stars.list_result] at H'
  exact H'

theorem aperture (ρ : ℝ) (hρ : 0≤ρ) (z : ℕ) :
    Real.exp (-ρ*((z/100000:ℕ):ℝ))≤Real.exp ρ*Real.exp (-(ρ/100000)*(z:ℝ)) := by
  rw [←Real.exp_add,Real.exp_le_exp]
  have h : (z:ℝ)≤100000*((z/100000:ℕ):ℝ)+100000 := by
    exact_mod_cast (show z≤100000*(z/100000)+100000 by omega)
  nlinarith only [mul_le_mul_of_nonneg_left h hρ]

open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe

/-- Original selected stage, simultaneously over its actual terminal depth,
physical periods and forest draws. All constants precede those choices. -/
theorem selected (R : Run G) (m n : ℕ) :
    ∃ δ M ρ : ℝ, 0<δ ∧ 0<M ∧ 0<ρ ∧ ∀ (N p : ℕ) (_hm : m<N),
      let S := R.alloy.B.a.clock.op m p
      let T := Pressure.Testing.ships R.alloy.B N m p
      let θ := R.alloy.B.a.clock.hatBeta m
      ∀ (_F : Forest S.ratio) (i : Slots S) (k : ℕ), k≤n → ∀ l : Fin k→FreeResolvent.Affine.raw G _,
        Real.exp (δ*Stars.rays (native _) (root S i) (FreeResolvent.Affine.hearth∘l))*
        ‖iteratedFDeriv ℝ k (fun B => ConditionalAffineSourceSplit.difference T θ B i)
          0 (FreeResolvent.Affine.ray G _∘l)‖≤M*Real.exp (-ρ*(radiusB θ:ℝ)) := by
  let A := R.alloy.B
  let P := Pressure.Testing.query R.metals.p R.metals.K (A.a.clock.J (m+1)) (A.a.clock.J m)
  let L := R.rolls.L (A.a.clock.J (m+1))
  obtain ⟨δ,M,hδ,hM,hρ,H⟩ := raw G P L n
  refine ⟨δ,M*Real.exp (rate P L),rate P L/100000,hδ,mul_pos hM (Real.exp_pos _),div_pos hρ (by norm_num),?_⟩
  intro N p hm S T θ F i k hk l
  have hP : P.Funds S T := Pressure.Testing.proceeds A N m p hm
  have hL : S.patch.L=L := by
    change A.a.S.block m=_
    rw [←A.a.fits.sameFactor m,A.valid.lengths]
  have hx : 0<temp θ := Work.E09.temp_pos (zero_lt_one.trans (A.a.fits.delayed m))
  have hh := H S T hP hL F θ hx i k hk l
  apply hh.trans
  simpa only [till,mul_assoc] using mul_le_mul_of_nonneg_left (aperture (rate P L) hρ.le (radiusB θ)) hM.le

end YM.Integration.ConditionalAffineSourcePrices

/-! Original physical row and field positions summed with an arbitrary
retained hit, in the actual periodic nearest-neighbor lattice metric. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineSourcePositions
open Function Filter Set Lattice Wilson RG Precision Exterior Tree Bloch Matrix Pressure Pressure.Tube Pressure.Stores
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Stars ConditionalAffineSourcePrices
open scoped BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}

def rowCost (L : Side) (γ : ℝ) := (Fintype.card Signed:ℝ)*(torusPay (Co L Layers2) γ+torusPay Axis γ)

theorem row_volume (S : StepData c f) (γ : ℝ) (hγ : 0<γ) :
    (native c).Volume (root S) γ (rowCost S.patch.L γ) := by
  constructor
  intro x
  have mask (s : Signed) (y : Site c) : (native c).weight (-γ) x (s.act y) =
      (native c).weight (-γ) (s.actEquiv.symm x) y := by
    have h : separation x (s.act y) = separation (s.actEquiv.symm x) y := by
      simpa only [show s.act (s.actEquiv.symm x)=x from s.actEquiv.apply_symm_apply x] using separation_signed (s.actEquiv.symm x) y s
    change Real.exp (-γ*(separation x (s.act y):ℝ))=Real.exp (-γ*(separation (s.actEquiv.symm x) y:ℝ))
    rw [h]
  let E := (Work.E03.meshEquiv f).trans (splitCo S.ratio Layers2)
  have cell (y : Site c) : ∑ j : Twin f, (native c).weight (-γ) y (S.ratio.parent j.1.1)≤torusPay (Co S.patch.L Layers2) γ := by
    have h := (E.sum_comp (fun j => (native c).weight (-γ) y j.1)).le.trans
      ((volume c (Co S.patch.L Layers2) γ hγ).bound y)
    have origin (j : Twin f) : ((Work.E03.meshEquiv f) j).1=j.1.1 := by
      rcases j with ⟨⟨y,a⟩,u⟩
      cases u <;> rfl
    simpa only [E,Equiv.trans_apply,split_co,origin] using h
  have bond (y : Site c) : ∑ j : Bond c, (native c).weight (-γ) y j.1≤torusPay Axis γ := (volume c Axis γ hγ).bound y
  change (∑ i : Signed × (Twin f ⊕ Bond c), (native c).weight (-γ) x (i.1.act (i.2.elim (fun h => S.ratio.parent h.1.1) (fun h => h.1))))≤_
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ _s : Signed, (torusPay (Co S.patch.L Layers2) γ+torusPay Axis γ) := by
      apply Finset.sum_le_sum
      intro s _
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl,Sum.elim_inr,mask]
      exact add_le_add (cell _) (bond _)
    _ = rowCost S.patch.L γ := by simp only [rowCost,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

def visit (S : StepData c f) (x : Site c) (i : Slots S) (j : FreeResolvent.Affine.raw G c) (l : Fin k→FreeResolvent.Affine.raw G c) : Bool :=
  decide (x=root S i ∨ x=hearth j ∨ ∃ z, x=hearth (l z))

def normEntry (T : Tube G S) (θ : ℝ) (i : Slots S) (j : FreeResolvent.Affine.raw G c) (l : Fin k→FreeResolvent.Affine.raw G c) : ℝ :=
  ‖iteratedFDeriv ℝ (k+1) (fun B => ConditionalAffineSourceSplit.difference T θ B i) 0 (ray G c ∘ Fin.cons j l)‖

/-- Every nonconstant tensor retains the original row or any specified
field hit. The two endpoints here are the actual signed row and the first
genuine marked field. There are exactly k further independently chosen fields. -/
theorem positions (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) : ∃ γ M V : ℝ, 0<γ ∧ 0<M ∧ 0≤V ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (_F : Forest S.ratio)
     (θ : ℝ), 0<temp θ → ∀ (k : ℕ), k+1≤n → ∀ y : Site c,
       NearStar k (taxi c) (root S) hearth hearth y (visit S y) (γ/4)
         (crowd k (M*Real.exp (-rate P L*(till θ:ℝ))) V) (normEntry T θ) := by
  obtain ⟨δ,M,hδ,hM,hρ,H⟩ := ConditionalAffineSourcePrices.raw G P L n
  let γ := δ/(2*(n+3:ℕ))
  have hγ : 0<γ := div_pos hδ (by positivity)
  let V := max (rowCost L γ) (torusPay (PAC G 1) γ)
  have hV : 0≤V := (torusPay_nn (PAC G 1) γ hγ).trans (le_max_right ..)
  refine ⟨γ,M,V,hγ,hM,hV,?_⟩
  intro c f S T hP hL F θ hθ k hk y
  have hSv := (row_volume S γ hγ).le (N:=V) (by rw [hL]; exact le_max_left ..)
  have hC : (native c).Volume (hearth (G:=G) (c:=c) (r:=1)) γ V := (volume c (PAC G 1) γ hγ).le (le_max_right ..)
  have hη : 2*(k+3:ℕ)*γ≤δ := by
    have hc : (0:ℝ)<2*(n+3:ℕ) := by positivity
    have ht : γ*((2*(n+3:ℕ)):ℝ)=δ := div_mul_cancel₀ δ hc.ne'
    have hkn : ((2*(k+3:ℕ)):ℝ)≤2*(n+3:ℕ) := by exact_mod_cast (show 2*(k+3)≤2*(n+3) by omega)
    simpa only [←ht,mul_comm] using mul_le_mul_of_nonneg_right hkn hγ.le
  apply ConditionalCovarianceLayers.nearest_neighbor hγ.le
  refine sums_no_mark hγ.le (mul_nonneg hM.le (Real.exp_pos _).le) hη hV ?_ ?_ hSv hC hC
  · intro i j l
    have h := H S T hP hL F θ hθ i (k+1) hk (Fin.cons j l)
    have eq : Stars.costs (native c) (root S i) (root S i) (hearth j) (hearth∘l) = rays (native c) (root S i) (hearth∘Fin.cons j l) := by
      unfold Stars.costs Stars.rays
      rw [(native c).self,zero_add,Fin.sum_univ_succ]
      rfl
    rw [eq,show |normEntry T θ i j l|=normEntry T θ i j l from abs_of_nonneg (norm_nonneg _)]
    exact h
  intro i j l h
  simpa only [visit,decide_eq_true_eq] using h


open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe

/-- The true absolute position sum at the selected no-hole stage, including the whole periodic route cost. -/
theorem selected (R : Run G) (m n : ℕ) :
    ∃ γ C V μ : ℝ, 0<γ ∧ 0<C ∧ 0≤V ∧ 0<μ ∧ ∀ (N p : ℕ) (_hm : m<N),
      let S := R.alloy.B.a.clock.op m p
      let T := Pressure.Testing.ships R.alloy.B N m p
      let θ := R.alloy.B.a.clock.hatBeta m
      ∀ (_F : Forest S.ratio) (k : ℕ), k+1≤n → ∀ y,
        NearStar k (taxi _) (root S) hearth hearth y (visit S y) (γ/4)
          (crowd k (C*Real.exp (-μ*(radiusB θ:ℝ))) V) (normEntry T θ) := by
  let A := R.alloy.B
  let P := Pressure.Testing.query R.metals.p R.metals.K (A.a.clock.J (m+1)) (A.a.clock.J m)
  let L := R.rolls.L (A.a.clock.J (m+1))
  obtain ⟨γ,C,V,hγ,hC,hV,H⟩ := positions G P L n
  have hρ := rate_pos P L
  refine ⟨γ,C*Real.exp (rate P L),V,rate P L/100000,hγ,mul_pos hC (Real.exp_pos _),hV,
    div_pos hρ (by norm_num),?_⟩
  intro N p hm S T θ F k hk y
  have hP : P.Funds S T := Pressure.Testing.proceeds A N m p hm
  have hL : S.patch.L=L := by
    change A.a.S.block m=_
    rw [←A.a.fits.sameFactor m,A.valid.lengths]
  have hx : 0<temp θ := Work.E09.temp_pos (zero_lt_one.trans (A.a.fits.delayed m))
  have hh := H S T hP hL F θ hx k hk y
  refine ⟨hh.limit.trans ?_⟩
  unfold crowd
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [till,mul_assoc] using mul_le_mul_of_nonneg_left (aperture (rate P L) hρ.le (radiusB θ)) hC.le

end YM.Integration.ConditionalAffineSourcePositions
