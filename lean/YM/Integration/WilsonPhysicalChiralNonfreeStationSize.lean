import YM.Integration.WilsonMaxwellThermometerStationHeads

/-! A cutoff-uniform size for the entire original weak vote after its
actual thermal and engineering normalization, derived on its own wheel. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeStationSize
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.East Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East Trace.Physical.Germ
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerMaximalHead
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "road" => R.family.path.levels

private theorem budget {d:ℕ}(F:Labels.Frame G d)(ρ θ ε:ℝ)(x y p:F.Coeff)
    (scale:1≤ρ)(pos:0<θ)(small:θ≤1)(half:ε<1)
    (eqn:∀i:F.Index,(θ:ℂ)^(F.grades i).2*y i=(ρ:ℂ)^(F.grades i).1*p i)
    (rent:F.coeffSize (x-y)≤ε*F.coeffSize x):
    θ^(d/2)/ρ^d*F.coeffSize x≤F.coeffSize p/(1-ε):=by
  let χ:=θ^(d/2)/ρ^d
  have rpos:0<ρ:=zero_lt_one.trans_le scale
  have dome:0<ρ^d:=pow_pos rpos _
  have hχ:0≤χ:=div_nonneg (pow_nonneg pos.le _) dome.le
  have allowance:χ*F.coeffSize y≤F.coeffSize p:=by
    change θ^(d/2)/ρ^d*(∑i,‖y i‖)≤∑i,‖p i‖
    rw [div_mul_eq_mul_div,div_le_iff₀ dome,mul_comm (∑i:F.Index,‖p i‖),Finset.mul_sum,Finset.mul_sum]
    apply sum_le_sum;intro i _
    have mode:=congrArg norm (eqn i)
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,abs_of_pos rpos] at mode
    calc θ^(d/2)*‖y i‖ ≤ θ^(F.grades i).2*‖y i‖ :=
           mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one pos.le small (rank F i)) (norm_nonneg _)
         _ = ρ^(F.grades i).1*‖p i‖ := mode
         _ ≤ ρ^d*‖p i‖ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ scale (F.bound i)) (norm_nonneg _)
  have tri:F.coeffSize x ≤ F.coeffSize (x-y)+F.coeffSize y:=by
    unfold Frame.coeffSize;rw [←sum_add_distrib];apply sum_le_sum; intro i _
    simpa only [Pi.sub_apply,sub_add_cancel] using (norm_add_le (x i-y i) (y i))
  have h1:=mul_le_mul_of_nonneg_left rent hχ
  have h2:=mul_le_mul_of_nonneg_left tri hχ
  change χ*F.coeffSize x≤F.coeffSize p/(1-ε)
  rw [le_div_iff₀ (sub_pos.mpr half)]
  nlinarith only [h1,h2,allowance]

section station
variable {C₁:Family G} {f:Extraction.Order} {H:(Bel C₁.book).Hierarchy}
private theorem onStation (h:C₁.Makes) {D:ℕ} (V:Vane C₁ D) (funded:V.checked f H D)
    (j:Fin (D+1)) (w:(Bel C₁.book).Field j) (N per:ℕ) (top:V.k<N)
    (scale:1≤Station.mag C₁.path.levels V.b V.k) (small:shrink C₁ V.k N per≤1)
    (half:Perch.bill (-1/2) (clim C₁.path.levels V.k)<1) :
    let θ:=shrink C₁ V.k N per
    let ρ:=Station.mag C₁.path.levels V.b V.k
    let p:=ladder C₁ j w
    let v:=V.wheel.atCut (N,per) j w
    let ε:=Perch.bill (-1/2) (clim C₁.path.levels V.k)
    θ^(j.val/2)/ρ^j.val*(C₁.labels.level j).coeffSize (awake C₁ j V.k N per v) ≤
      (C₁.labels.level j).coeffSize p/(1-ε):=by
  intro θ ρ p v ε
  obtain ⟨charts,sky⟩:=funded.rate N per top
  have solved: Solves C₁ ρ j V.k N per (V.R N per j) p v :=
    poured h (funded.early j) top.le ρ _ ((charts j).1) p
  apply budget (C₁.labels.level j) ρ θ ε _ ((V.R N per j) v) _ scale (shrink_pos C₁ h top.le per) small
    half _ (sky j v)
  intro i
  simpa only [Solves,Frame.scaled_apply,Complex.ofReal_pow,weightTag,LinearMap.coe_mk,AddHom.coe_mk]
    using congrFun solved i

end station
variable {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}

theorem original (simple:G.Simple):∀ᶠ k:ℕ in atTop, ∀ (A:Group C 6),
    A.station.k=k → A.station.checked f H A.horizon → ∀ N per, k<N →
    ∀ s (i:Fin 3),
    let j:=index A (grade i)
    let w:=A.change (grade i) (source C s i)
    let p:=ladder C j w
    let θ:=shrink C k N per
    let ρ:=Station.mag road A.station.b k
    let x:=awake C j k N per (A.station.wheel.atCut (N,per) j w)
    θ^(j.val/2)/ρ^j.val*((C).labels.level j).coeffSize x ≤
      ((C).labels.level j).coeffSize p/(1-WilsonMaxwellThermometerStationHeads.fee R k):=by
  filter_upwards [WilsonMaxwellThermometerStationHeads.clock R simple] with k paid
  intro A eqn checked N per hn s i
  subst k
  have enough:=paid.2.2 N per hn.le
  have θ:shrink C A.station.k N per≤1:=enough.2.trans ((div_le_one
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<2) paid.2.1)).mpr paid.2.1)
  have scale:1≤Station.mag road A.station.b A.station.k:=
    Real.one_le_rpow ((by norm_num:(1:ℝ)≤2).trans paid.2.1)
      (le_of_lt ((by norm_num:(0:ℝ)<5).trans checked.high.1))
  exact onStation R.makes A.station checked (index A (grade i)) _ N per hn scale θ paid.1


end YM.Integration.WilsonPhysicalChiralNonfreeStationSize
