import YM.Integration.WilsonLongContactHymnPlay
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Hymn

/-! Exchange and differentiation on the originally normalized, tagged Gaussian
with a fixed compact fine field and an arbitrary finite rooted coefficient. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonLongContactHymn
open PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad PhysicalNext
open PhysicalNext.JointLoad.Heir.Museum
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    Push.SectorMeasure SelectedOrderedKernels SelectedOrderedKernels.Sector Next.SectorChange.Rows Wisps
    Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussianLaws
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}

variable {Γ : Prices G ι → ℝ} (T k q d u) (a : Museum F x A X Y ι) (U : Config G f)

variable {T k q d u} (he : Plays C D P B Pt T x) (origin : o∈X) (regular : B.Regular X f') (hτ : B.supBounds o X f' τ)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ) (hV : Healthy P.threshold Y V)
include he origin regular hτ hY hu hΓ hV

lemma civil (μ : Measure (Prices G ι)) [IsFiniteMeasure μ] : Covered μ (fun z => a.concert T u q d k f' Γ U V z ∘ increment V) n 0 := by
  letI : ProperSpace (Directions G c) := FiniteDimensional.proper ℝ _
  have ha := he.cantos (k:=k) a hV hY origin
  refine domeCovered hΓ.finite (fun z hz => funext fun _ => by simp [concert,image_eq_zero_of_notMem_tsupport hz]) (fun z hz => ?_)
  have hc := prior (q:=q) (d:=d) (k:=k) he a origin regular hV U z hu (hΓ.stay z hz) hτ |>.1
  have hh : ContDiffAt ℝ n (fun p : Directions G c × Prices G ι => Carillon.vary V (a.twilight k T) p.2 (increment V p.1)*Γ p.2) (0,z) := (ha.joint z).mul (hΓ.real.contDiffAt.comp _ contDiffAt_snd)
  unfold concert; simp only [Function.comp_apply, ← Complex.ofReal_mul]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hh.mul hc)

lemma exchange (L : List (Directions G c)) (hl : L.length ≤ n) :
    let h := a.hymn T u q d k f' Γ U
    let b := a.concert T u q d k f' Γ U V
    let μ := Gaussian.cloud (a.twilight k T V)
    Multi.Puff.Crest n h V ∧ Integrable (fun z => leftDerivs (b z) L V) μ ∧ ((leftDerivs h L V : ℝ):ℂ) = ∫ z,leftDerivs (b z) L V ∂μ := by
  intro h b μ; have ha := he.cantos (k:=k) a hV hY origin
  have ht : ((fun U => (h U:ℂ)) ∘ increment V) =ᶠ[𝓝 0] fun v => ∫ z,b z (increment V v) ∂μ := by
    have hy := Multi.Puff.inc_tr V |>.tendsto 0; rw [Work.G07.at_zero_increment] at hy
    filter_upwards [hy.eventually ha.near] with v hv
    have hh := Density.exchange _ _ hv ha.pos (0:Prices G ι) (fun z => Γ z * f' (a.received k T q d u (increment V v) U z))
    unfold h hymn; rw [Function.comp_apply,if_pos hv,hh.2,← integral_complex_ofReal]; congr! 1; ext1 z; simp [Density.priced,Carillon.vary,b,concert,mul_assoc]
  have hc := civil a U he origin regular hτ hY hu hΓ hV μ (k:=k) (q:=q) (d:=d)
  obtain ⟨hQ,hI,hL⟩ := left_integral V L.get hl hc ht
  have hb : ∀ᵐ z ∂μ, leftDerivs (b z) L V=iteratedFDeriv ℝ L.length (b z ∘ journey V L.length L.get) 0 cart := hc.ae.mono (fun z hz => by
    simpa only [List.ofFn_get] using Germ.ordered L.get ((show Germ n (b z) V from hz).prod hl))
  have hr : Multi.Puff.Crest n h V := crest_cast.mp (Multi.Puff.into n _ hQ)
  refine ⟨hr,hI.congr (hb.mono fun _ hx => hx.symm),?_⟩
  rw [List.ofFn_get] at hL; rw [show ((leftDerivs h L V:ℝ):ℂ)=leftDerivs (fun U => (h U:ℂ)) L V from (Push.Local.left_linear Complex.ofRealCLM L hr.germ hl).symm, hL]
  exact integral_congr_ae (hb.mono fun _ hx => hx.symm)

omit [DecidableEq ι] hY in
private lemma e_band {z : Prices G ι} (hz : z∈tsupport Γ) :
    Band n (P.dirBound (S.ratio.parent o)) V 1 (grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n * τ) (fun V => (f' (a.received k T q d u V U z):ℂ)) := by
  let f : Config G c → ℝ := fun V => f' (a.received k T q d u V U z)
  obtain ⟨h,hc⟩ := prior (k:=k) (q:=q) (d:=d) he a origin regular hV U z hu (hΓ.stay z hz) hτ
  have h' : Germ n f V := ContDiffAt.comp (f:=fun p : Directions G c => (p,z)) 0 h (contDiffAt_id.prodMk contDiffAt_const)
  let cost := grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n * τ
  have hp (l : List (Directions G c)) (hl : l.length ≤ n) (hb : ∀ A∈l,P.dirBound (S.ratio.parent o) A) : ‖leftDerivs (Complex.ofRealCLM ∘ f) l V‖ ≤ cost := by
    rw [Push.Local.left_linear Complex.ofRealCLM l (show Push.Local.Chart n f V from h') hl, show leftDerivs f l V = iteratedFDeriv ℝ l.length (f ∘ journey V l.length l.get) 0 cart by simpa only [List.ofFn_get] using Germ.ordered l.get (h'.prod hl)]
    rw [show ∀ x:ℝ,‖Complex.ofRealCLM x‖=‖x‖ from fun _ => Complex.norm_real _]
    simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hc l.length hl l.get (fun i => hb _ (List.get_mem ..))) (show ∀ i:Fin l.length,‖cart i‖ ≤ (1:ℝ) from fun i => (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by simp only [cart,Pi.single_apply]; split <;> norm_num))
  exact ⟨crest_cast.mpr (Multi.Puff.into _ f h'),zero_le_one,(norm_nonneg _).trans (hp [] (Nat.zero_le _) (List.forall_mem_nil _)),fun l hl hb => by simpa using! hp l hl hb⟩

omit he origin regular hτ hY hu hΓ hV in
private theorem quote_nonneg (hτ : 0≤τ) :
    0≤grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n * τ := by
  have hh := ample_one n X P B D.majorant C.matins C.C_one (x:=x)
  unfold grandFee
  positivity [patterns_nonneg n, C.rights.large]

theorem choir_band (z : Prices G ι) : let R := scope B X r x; let m := 1+Carillon.speed n D.Z B.threshold P.power R z
    Band n (P.dirBound (S.ratio.parent o)) V m (grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n*τ) (a.concert T u q d k f' Γ U V z) := by
  intro R m
  have ha := he.cantos (k:=k) a hV hY origin
  have hy := ha.sing B.threshold_pos.le B.threshold_le D.chimes z
  change Band n (P.dirBound _) V (Carillon.speed n D.Z B.threshold P.power R z) 1 _ at hy
  by_cases hz : z∈tsupport Γ
  · have hf' := e_band a U he origin regular hτ hu hΓ hV hz (k:=k) (q:=q) (d:=d)
    have heq : a.concert T u q d k f' Γ U V z = ((Γ z:ℂ) • fun W => (Carillon.vary V (a.twilight k T) z W:ℂ)) * (fun W => (f' (a.received k T q d u W U z):ℂ)) := by
      ext1 W; simp [concert, mul_comm]
    rw [heq, show m=Carillon.speed n D.Z B.threshold P.power R z+1 from add_comm ..]
    exact band_rise ((hy.scale (Γ z:ℂ)).multiply hf') (by rw [Complex.norm_real,mul_one]; exact mul_le_of_le_one_left hf'.nonneg (hΓ.little _)) le_rfl
  rw [show a.concert T u q d k f' Γ U V z = (fun _ => (0:ℂ)) from funext fun _ => by simp [concert,image_eq_zero_of_notMem_tsupport hz]]
  exact band_rise (band_constant n _ (r:=m) (by have := hy.sane; unfold m; positivity)) (by rw [norm_zero]; exact quote_nonneg hτ.1) le_rfl

end YM.Integration.WilsonLongContactHymn
