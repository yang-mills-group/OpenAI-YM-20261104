import YM.Integration.WilsonSeparatedCompactDiagnostic
import YM.Integration.WilsonSeparatedReportedGram

/-! The *unrounded* physical pivot/mixed correlation at diagnostic
separation r=a_m Λ_m^B on every compact separated continuum profile.
Screened rounding is used only for the actual cutoff tensor Z. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedContinuousGram
open Function Filter Finset Set Metric MeasureTheory Lattice Extraction Table Spec
open Next.Rank OPE OPE.Orbits OPE.Nesting RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Frontier6.Road Trace.Pilot SharedIntrinsicWilsonGrid ContinuumIntrinsicWilsonProduct IntrinsicWilsonTensor
open WilsonSeparatedDiagnosticGram
open scoped Classical BigOperators Topology
universe u
variable {G : Gauge} {C : Family G} {S : Table C.book} {R : Run G} {f : Extraction.Order}
variable {V : Table R.family.book}

private theorem scale (C : Family G) (hG : G.Simple) (B:ℝ) :
    RateIs atTop C.S.scale (WilsonSeparatedReportedGram.length C B) (-1) := by
  have hh := ((RG16.Literal.levelT C hG).rpow B).mul (RG16.Literal.normal_height C).mesh
  change RateIs atTop C.S.scale (fun m=>(RG16.Lambda C.path.levels m)^B*C.S.a m) (-1)
  simpa only [mul_zero,zero_add,id_eq] using hh

private theorem toward (C : Family G) (hG : G.Simple) (B:ℝ) :
    Tendsto (WilsonSeparatedReportedGram.length C B) atTop trail :=
  tendsto_nhdsWithin_iff.mpr ⟨(scale C hG B).tends (by norm_num) C.S.divergent,(scale C hG B).pos⟩

private theorem overlay (C : Family G) (hG : G.Simple) (B w:ℝ) {δ:ℝ} (δp:0<δ) :
    ∀ᶠ m:ℕ in atTop,(RG16.Lambda C.path.levels m)^w ≤ (WilsonSeparatedReportedGram.length C B m)^(-δ) := by
  have h := ((scale C hG B).rpow (-δ)).overtakes (((RG16.Literal.levelT C hG).rpow w).pays C.S.divergent)
    C.S.divergent (by simpa only [mul_zero,mul_neg,mul_one,neg_neg] using δp)
  exact h.mono fun _ v=>v.le

private theorem weights {I:Type} [Fintype I] (F : Final C f S) (hG : G.Simple)
    (J : ℝ → tower S) (H : Leading F J) (d:I→ℕ) (B:ℝ) :
    ∃ K:ℝ,0≤K ∧ ∀ᶠ m:ℕ in atTop,∀ b:I→ℝ,(∀ i,b i∈Icc (0:ℝ) B) →
      ∀ v:(i:I)→Input C (d i),
        (∏ i,‖WilsonSeparatedReportedGram.inputs J m B b v i‖) ≤
        K*(RG16.Lambda C.path.levels m)^(B*(Fintype.card I:ℝ))*∏ i,‖v i‖ := by
  choose K high room using fun i=>WilsonSeparatedForwardFrame.between F (d i) J H zero_lt_one
  refine ⟨∏ i,K i,Finset.prod_nonneg (fun i _=>zero_le_one.trans (high i)),?_⟩
  filter_upwards [(toward C hG B).eventually (eventually_all.mpr room)] with m enter b bound v
  let L := RG16.Lambda C.path.levels m
  let r := WilsonSeparatedReportedGram.length C B m
  let t (i:I) := L^(b i-B)
  have lp : 0<L := RG16.Literal.lambda_pos C m
  have big : 1≤L := one_le_two.trans (RG16.Literal.lambda_up C m).le
  have stay (i:I) : t i∈Ioc (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos lp _,Real.rpow_le_one_of_one_le_of_nonpos big (sub_nonpos.mpr (bound i).2)⟩
  have located (i:I) : t i*r=WilsonSeparatedReportedGram.length C (b i) m := by
    change L^(b i-B)*(L^B*C.S.a m)=L^(b i)*C.S.a m
    rw [←mul_assoc,←Real.rpow_add lp,sub_add_cancel]
  have fee (i:I) : (t i)^(-(1:ℝ)) ≤ L^B := by
    dsimp only [t]
    rw [←Real.rpow_mul lp.le]
    exact Real.rpow_le_rpow_of_exponent_le big (by linarith only [(bound i).1])
  have slot (i:I) : ‖WilsonSeparatedReportedGram.inputs J m B b v i‖ ≤ (K i*L^B)*‖v i‖ := by
    have h := enter i (t i) (stay i) (J (t i*r) (d i) (v i))
    change ‖(J r (d i)).symm (J (t i*r) (d i) (v i))‖ ≤ K i*(t i)^(-(1:ℝ))*
      ‖(J (t i*r) (d i)).symm (J (t i*r) (d i) (v i))‖ at h
    rw [LinearEquiv.symm_apply_apply,located i] at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (fee i) (zero_le_one.trans (high i))) (norm_nonneg _))
  have all := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>norm_nonneg (WilsonSeparatedReportedGram.inputs J m B b v i))
    (fun i _=>slot i)
  change _ ≤ (∏ i,K i)*L^(B*(Fintype.card I:ℝ))*∏ i,‖v i‖
  rw [Real.rpow_mul lp.le,Real.rpow_natCast]
  simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] using all

/-- Each character, every earlier reporting frame, and every unrounded
separated continuum profile are allowed. The chosen Z is still the
native common limit of the whole finite original cutoff on *one* screen. -/
theorem original {T : Campaign R} (hG : G.Simple) (W : Campaign.Pillars R T) {z₀ : ℝ}
    (source : FundedOriginalProperties.{u} hG z₀ W) (pace : WilsonWindowReportingPace.Slow R.kit) {H:ℕ} (hH:0<H)
    (F : Final R.family f V) (fac : Facilities R.family f V)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J : ℝ → tower V) (lead : Leading F J)
    {A : (Bel R.family.book).Hierarchy} (paid : ∀ d : ℕ,∀ᶠ r in trail,Frame.obedient F A (J r) d)
    {n:ℕ} (d:Caps n) (anchor:Fin n) (P : Plan R.family 0 (Fintype.card (Fin n)) (∑ i,d i))
    {K : Set (Points n)} (compact : IsCompact K) (sep : K ⊆ conf n)
    {σ B:ℝ} (cap : σ<1/32) (resolution : σ<P.c-1) {g : ℝ→ℝ} (hg : Coupling G g)
    (k:ℕ) {ε:ℝ} (εp:0<ε) :
    ∀ᶠ m:ℕ in atTop,let r := WilsonSeparatedReportedGram.length R.family B m
      ∀ X∈K,let x := WilsonSeparatedProfileGrid.sites R.family.S (P.j r) r X
      (∃ Z:Tensor R.family d 0,Common F Q J r (P.b r) (P.j r) x Z) ∧
      ∀ Z:Tensor R.family d 0,Common F Q J r (P.b r) (P.j r) x Z →
        ∀ b:Fin n→ℝ,(∀ i,b i∈Icc (0:ℝ) B) → ∀ q:Viewers F,∀ v:(i:Fin n)→Input R.family (d i),
        let a := WilsonSeparatedReportedGram.inputs J m B b v
        Cluster F Q J a r (P.b r) (P.j r) x (Z a) ∧
          ‖Orbits.moment (spectator F q) (posed r X) (fun i=>J (WilsonSeparatedReportedGram.length R.family (b i) m)
                (d i) (v i))-scalar V V (V.project 0 (Z a))‖ ≤ ε*g r^k*r^σ*∏ i,‖v i‖ := by
  let θ := (max (0:ℝ) σ+(P.c-1))/2
  have ceiling : max (0:ℝ) σ<P.c-1 := max_lt (by linarith only [P.high]) resolution
  have above : max (0:ℝ) σ<θ := by dsimp only [θ]; linarith only [ceiling]
  have θp : 0<θ := (le_max_left ..).trans_lt above
  have θs : σ<θ := (le_max_right ..).trans_lt above
  have fit : 1+θ<P.c := by dsimp only [θ]; linarith only [ceiling]
  let δ := (θ-σ)/2
  have δp : 0<δ := by dsimp only [δ]; linarith only [θs]
  have roomFor : 0<θ-δ-σ := by dsimp only [δ]; linarith only [θs]
  obtain ⟨L,M,η,nL,ηp,distance⟩ := WilsonSeparatedCompactDiagnostic.original hG W source pace hH F fac Q J lead
    paid d P compact sep hg θp fit
  obtain ⟨E,nE,frames⟩ := weights F hG J lead d B
  have time := toward R.family hG B
  have physical := WilsonSeparatedReportedGram.original F fac anchor Q P J lead (M:=M) ηp cap hg k (half_pos εp) (B:=B)
  have owned := time.eventually (subpower_payment hg hG (L*E) (θ-δ-σ) roomFor (ε/2) (half_pos εp) k)
  filter_upwards [physical,time.eventually distance,frames,overlay R.family hG B (B*(Fintype.card (Fin n):ℝ)) δp,
    owned,(scale R.family hG B).pos] with m centre rounded columns overlayFee fee rp r X hx x
  change 0<r at rp
  have geometry := rounded X hx
  have cert := centre x geometry.1
  refine ⟨cert.1,?_⟩
  intro Z commonZ b earlier q v a
  let y := R.family.S.gridPoint (P.j r) ∘ x
  let fields : Labels V d := fun i=>J (WilsonSeparatedReportedGram.length R.family (b i) m) (d i) (v i)
  let Λ := RG16.Lambda R.family.path.levels m
  let Wt := B*(Fintype.card (Fin n):ℝ)
  let N := ∏ i,‖v i‖
  have nN : 0≤N := Finset.prod_nonneg fun i _=>norm_nonneg _
  have born : Frame.born J r a=fields := funext fun _=>LinearEquiv.apply_symm_apply ..
  have cutoff := cert.2 Z commonZ b earlier q (Or.inr geometry.2.1) v
  have shifted := geometry.2.2 q a
  rw [born] at shifted
  have change :
      ‖Orbits.moment (spectator F q) (posed r X) fields-Orbits.moment (spectator F q) y fields‖ ≤
        (ε/2)*g r^k*r^σ*N := by
    calc
      _ ≤ L*r^θ*(∏ i,‖a i‖) := shifted
      _ ≤ L*r^θ*(E*Λ^Wt*N) := mul_le_mul_of_nonneg_left (columns b earlier v)
        (mul_nonneg nL (Real.rpow_nonneg rp.le _))
      _ ≤ L*r^θ*(E*r^(-δ)*N) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left overlayFee nE) nN)
        (mul_nonneg nL (Real.rpow_nonneg rp.le _))
      _ = ((L*E)*r^(θ-δ-σ))*r^σ*N := by
        have ex : r^θ*r^(-δ)=r^(θ-δ-σ)*r^σ := by rw [←Real.rpow_add rp,←Real.rpow_add rp]; congr 1; ring
        linear_combination L*E*N*ex
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right fee (Real.rpow_nonneg rp.le _)) nN
  refine ⟨cutoff.1,?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ (Orbits.moment (spectator F q) y fields) _).trans
    ((add_le_add change cutoff.2).trans_eq (by dsimp only [N]; ring))

end YM.Integration.WilsonSeparatedContinuousGram
