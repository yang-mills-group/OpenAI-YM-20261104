import YM.Integration.WilsonSeparatedDiagnosticGram

/-! The original numerical pivot/mixed Gram at diagnostic separation r
can use its own independently chosen earlier reporting mesh in every
slot. The same actual cutoff sublimit works for every such choice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedDiagnosticFrames
open Function Filter Set Lattice Wilson Cells Spec Climb OPE OPE.Orbits OPE.Cards PhysMS
open Frontier6.Road Trace.Pilot SharedIntrinsicWilsonGrid ContinuumIntrinsicWilsonProduct IntrinsicWilsonTensor
open WilsonSeparatedDiagnosticGram
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ}

def inputs (J : ℝ → tower S) (r:ℝ) (t:I→ℝ) (v:(i:I)→Input C (d i)) (i:I) : Input C (d i) :=
  (J r (d i)).symm (J (t i*r) (d i) (v i))

omit [Fintype I] in
theorem actual (J : ℝ → tower S) (r:ℝ) (t:I→ℝ) (v:(i:I)→Input C (d i)) :
    Frame.born J r (inputs J r t v) = fun i=>J (t i*r) (d i) (v i) :=
  funext fun _=>LinearEquiv.apply_symm_apply ..

/-- The actual unit-channel discrepancy on all observations, retaining the
explicit per-column (earlier length / diagnostic length)^(-δ) cost. -/
theorem priced (F : Final C f S) (fac : Facilities C f S) (anchor:I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C 0 (Fintype.card I) (∑ i,d i)) (J : ℝ → tower S) (H : Leading F J)
    {M η σ δ : ℝ} (ηp : 0<η) (roomFor : σ<1/32) (δp : 0<δ) {g : ℝ → ℝ} (hg : Coupling G g)
    (k:ℕ) {ε:ℝ} (εp : 0<ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, WithinRoom r M η (C.S.gridPoint (P.j r) ∘ x) 0 →
      (∃ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z) ∧
      ∀ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z →
        let y := C.S.gridPoint (P.j r) ∘ x
        ∀ t : I → ℝ,(∀ i,t i∈Ioc (0:ℝ) 1) → ∀ q : Viewers F,q=none ∨ Screen y →
          ∀ v : (i:I)→Input C (d i),let a := inputs J r t v
          Cluster F Q J a r (P.b r) (P.j r) x (Z a) ∧
          ‖Orbits.moment (spectator F q) y (fun i=>J (t i*r) (d i) (v i))-scalar S S (S.project 0 (Z a))‖ ≤
            ε*g r^k*r^σ*(∏ i,t i^(-δ))*∏ i,‖v i‖ := by
  classical
  choose K one fees using fun i=>WilsonSeparatedForwardFrame.between F (d i) J H δp
  let B := ∏ i,K i
  have nb : 0≤B := Finset.prod_nonneg fun i _=>zero_le_one.trans (one i)
  let ε' := ε/(1+B)
  have small : 0<ε' := div_pos εp (by linarith only [nb])
  have net : B*ε'≤ε := by
    dsimp only [ε']
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith only [nb])).mpr
    nlinarith only [εp.le]
  filter_upwards [diagnostic F fac anchor Q P J H ηp roomFor hg k small,eventually_all.mpr fees,
    length_rate.pos,hg.positive] with r admitted bought rp gp x geom
  have cut := admitted x geom
  refine ⟨cut.1,?_⟩
  intro Z has y t tset q channel v a
  have slot (i:I) : ‖a i‖ ≤ (K i*(t i)^(-δ))*‖v i‖ := by
    have h := bought i (t i) (tset i) (J (t i*r) (d i) (v i))
    change ‖(J r (d i)).symm (J (t i*r) (d i) (v i))‖ ≤ _
    simpa only [LinearEquiv.symm_apply_apply] using h
  let T := ∏ i,t i^(-δ)
  let V := ∏ i,‖v i‖
  have upper : (∏ i,‖a i‖) ≤ (B*T)*V := by
    have h := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>norm_nonneg (a i)) (fun i _=>slot i)
    simpa only [Finset.prod_mul_distrib] using h
  have posT : 0≤T := Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (tset i).1.le _)
  have posV : 0≤V := Finset.prod_nonneg fun i _=>norm_nonneg _
  have posW : 0≤g r^k*r^σ := mul_nonneg (pow_nonneg gp.le _) (Real.rpow_nonneg rp.le _)
  have cb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right net posW) posT) posV
  refine ⟨has.cluster a,?_⟩
  rw [←actual J r t v]
  calc
    _ ≤ ε'*g r^k*r^σ*(∏ i,‖a i‖) := cut.2 Z has q channel a
    _ ≤ ε'*g r^k*r^σ*((B*T)*V) := mul_le_mul_of_nonneg_left upper
      (mul_nonneg (mul_nonneg small.le (pow_nonneg gp.le _)) (Real.rpow_nonneg rp.le _))
    _ = ((B*ε')*(g r^k*r^σ))*T*V := by ring
    _ ≤ _ := cb.trans_eq (by dsimp only [T,V]; ring)

/-- A uniform price for diagnostic/reporting ratios up to any fixed power
of 1/r, including bounded powers of a logarithmic reporting factor. The
early mesh may differ in every slot. -/
theorem original (F : Final C f S) (fac : Facilities C f S) (anchor:I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C 0 (Fintype.card I) (∑ i,d i)) (J : ℝ → tower S) (H : Leading F J)
    {M η σ A : ℝ} (ηp : 0<η) (roomFor : σ<1/32) (An : 0≤A)
    {g : ℝ → ℝ} (hg : Coupling G g) (k:ℕ) {ε:ℝ} (εp : 0<ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, WithinRoom r M η (C.S.gridPoint (P.j r) ∘ x) 0 →
      (∃ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z) ∧
      ∀ Z:Tensor C d 0,Common F Q J r (P.b r) (P.j r) x Z →
        let y := C.S.gridPoint (P.j r) ∘ x
        ∀ t : I → ℝ,(∀ i,t i∈Icc (r^A) 1) → ∀ q : Viewers F,q=none ∨ Screen y →
          ∀ v : (i:I)→Input C (d i),let a := inputs J r t v
          Cluster F Q J a r (P.b r) (P.j r) x (Z a) ∧
          ‖Orbits.moment (spectator F q) y (fun i=>J (t i*r) (d i) (v i))-scalar S S (S.project 0 (Z a))‖ ≤
            ε*g r^k*r^σ*∏ i,‖v i‖ := by
  let n : ℝ := Fintype.card I
  let γ := (σ+1/32)/2
  have g1 : σ<γ := by dsimp only [γ]; linarith only [roomFor]
  have g2 : γ<1/32 := by dsimp only [γ]; linarith only [roomFor]
  have np : 0≤n := Nat.cast_nonneg _
  have divp : 0<1+A*n := by nlinarith only [mul_nonneg An np]
  let δ := (γ-σ)/(1+A*n)
  have δp : 0<δ := div_pos (sub_pos.mpr g1) divp
  have reserve : σ≤γ+(-A*δ)*n := by
    have eq : δ*(1+A*n)=γ-σ := div_mul_cancel₀ _ divp.ne'
    nlinarith only [eq,δp.le]
  filter_upwards [priced F fac anchor Q P J H ηp g2 δp hg k εp,length_rate.pos,hg.positive,
    (gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
       (@nhdsWithin_le_nhds ℝ _ (0:ℝ) (Ioi (0:ℝ)))] with r admit rp gp atMost x geom
  change 0<r at rp
  change r<1 at atMost
  have cut := admit x geom
  refine ⟨cut.1,?_⟩
  intro Z existsZ y t tset q channel v a
  have stay (i:I) : t i∈Ioc (0:ℝ) 1 := ⟨(Real.rpow_pos_of_pos rp A).trans_le (tset i).1,(tset i).2⟩
  have results := cut.2 Z existsZ t stay q channel v
  have slot (i:I) : (t i)^(-δ) ≤ r^(-A*δ) := calc
    _ ≤ (r^A)^(-δ) := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos rp A) (tset i).1 (neg_nonpos.mpr δp.le)
    _ = _ := by rw [←Real.rpow_mul rp.le]; congr 1; ring
  have prod : (∏ i,t i^(-δ)) ≤ r^((-A*δ)*n) := by
    have h := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>Real.rpow_nonneg (stay i).1.le (-δ)) (fun i _=>slot i)
    simpa only [Finset.prod_const,Finset.card_univ,Real.rpow_mul rp.le,Real.rpow_natCast,n] using h
  have power := (mul_le_mul_of_nonneg_left prod (Real.rpow_nonneg rp.le γ)).trans
    (show r^γ*r^((-A*δ)*n) ≤ r^σ by rw [←Real.rpow_add rp]; exact Real.rpow_le_rpow_of_exponent_ge rp atMost.le reserve)
  have short := mul_le_mul_of_nonneg_left power (mul_nonneg εp.le (pow_nonneg gp.le k))
  refine ⟨results.1,results.2.trans ?_⟩
  rw [mul_assoc (ε*g r^k) (r^γ)]
  exact mul_le_mul_of_nonneg_right short (Finset.prod_nonneg fun i _=>norm_nonneg (v i))

end YM.Integration.WilsonSeparatedDiagnosticFrames
