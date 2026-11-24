import YM.Integration.WilsonPhysicalExteriorRichFarCells

/-! The presold positive far detector integrates the actual R-rich signed
coefficients. The finite weights are precisely the normalized original
center smears, including both the physical side and the auxiliary side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarDeposit
open Function Filter Set Finset Real MeasureTheory Lattice RG RG16 Pert Pert.Position
open XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 FVA2 MS MS.Land MS.Menus MS.Tone MS.Dial MS.Rake MS.Logarithm
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorQuadratureClock WilsonPhysicalExteriorFirstCutScale
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorRichFarCells
open scoped Topology BigOperators Classical
variable {n:ℕ} {G:Gauge}
variable (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (Q:Prescription (Press.portDeck G))
local notation "B₀" => Press.portDeck G
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

def reading (D:Fin (n+1)→Label B₀) (g:Test (n+1)) (c c':ℝ) (s:Bool) (u:ℝ) (k j per:ℕ) : ℂ:=
  Deposit (grid R c c' true s (j,per)) (fun v=>MSExteriorDilation.power (MSExteriorDilation.weight D)
    (log (T₀ c' j))*cell R Q D c s u k j per v) g

private def independent (D:Fin (n+1)→Label B₀) (ν:ℝ) (k:ℕ) (v:Sample (n+1)) : ℂ:=
  MSExteriorDilation.moment M D ν (Fountain.metric (v.F.rel v.layout 0)) k

private theorem common (D:Fin (n+1)→Label B₀) (ν:ℝ) (k:ℕ) (v:Sample (n+1))
    (hv:familiar v∈conf (n+1)) :
    MSExteriorDilation.moment M D ν (Fountain.metric (familiar v)) k=independent M D ν k v := by
  let x:=Fountain.metric (familiar v)
  let y:=Fountain.metric (v.F.rel v.layout 0)
  have h:∀ i l,x i-x l=y i-y l:=by
    intro i l;ext a
    change v.F.spacing*(v.layout i a:ℝ)-v.center a-(v.F.spacing*(v.layout l a:ℝ)-v.center a)=
      v.F.spacing*(v.layout i a:ℝ)-0-(v.F.spacing*(v.layout l a:ℝ)-0)
    ring
  have he:=Arrival.Schedule.transfers ν D M (x:=x) (y:=y) (Fountain.metric_conf hv) h
  unfold independent MSExteriorDilation.moment tour book
  change Puff.Mom.bouquet (fun t b=>Vane.blade (spine M D ν x t b) ()) univ k=
    Puff.Mom.bouquet (fun t b=>Vane.blade (spine M D ν y t b) ()) univ k
  rw [he]

private theorem drawn (D:Fin (n+1)→Label B₀) (g:Test (n+1)) (m:Mesh) (ν:ℝ) (k:ℕ) :
    WilsonPhysicalExteriorMSQuadrature.quadrature m g
      (fun x=>MSExteriorDilation.moment M D ν (Fountain.metric x) k)=Deposit m (independent M D ν k) g := by
  rw [homeward,WilsonPhysicalExteriorMSQuadrature.quadrature]
  apply congrArg (fun t:ℂ=>(m.vol:ℂ)⁻¹*t)
  apply integral_congr_ae;filter_upwards [] with c
  rw [stroll,WilsonPhysicalExteriorMSQuadrature.corners]
  apply congrArg (fun t:ℂ=>(m.spacing:ℂ)^(4*(n+1))*t)
  apply sum_congr rfl;intro i _
  let v:Sample (n+1):=⟨m,m.back i,c⟩
  by_cases hz:familiar v∈tsupport g
  · exact congrArg (fun z:ℂ=>g (familiar v)*z) (common M D ν k v (g.tsupport_subset hz))
  · have zero:g (m.rel (m.back i) c)=0:=image_eq_zero_of_notMem_tsupport hz
    rw [zero,zero_mul,zero_mul]

private def mass (m:Mesh) (x:pack (n+1)) (g:Test (n+1)) : ℝ:=
  m.vol⁻¹*∫c in m.Box,(g (m.rel x c)).re

private theorem paid (m:Mesh) (x:pack (n+1)) (g:Test (n+1)) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) :
    m.smear x g=(mass m x g:ℂ) ∧ 0 ≤ mass m x g := by
  have surely (z:Points (n+1)):g z=((g z).re:ℂ):=Complex.ext rfl (by simpa using (good z).1)
  constructor
  · change (m.vol⁻¹:ℝ) • (∫c in m.Box,g (m.rel x c))=_
    have eq:(fun c=>g (m.rel x c))=(fun c=>((g (m.rel x c)).re:ℂ)):=funext fun c=>surely _
    rw [eq,integral_complex_ofReal,mass,Complex.ofReal_mul,Complex.real_smul]
  · exact mul_nonneg (inv_nonneg.mpr m.vol_pos.le) (integral_nonneg fun _=>(good _).2)

private theorem support {m:Mesh} {x:pack (n+1)} {g:Test (n+1)} (nz:m.smear x g≠0) :
    ∃c:Four ℝ,m.rel x c∈tsupport g := by
  by_contra! none
  have he: (fun c=>g (m.rel x c))=0:=funext fun c=>image_eq_zero_of_notMem_tsupport (none c)
  apply nz;change m.vol⁻¹ • (∫c in m.Box,g (m.rel x c))=0
  rw [he];simp

private theorem total (g:Test (n+1)) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) :
    ∃C:ℝ,0<C ∧ ∀ᶠ m:Mesh in Front,
      m.spacing^(4*(n+1))*∑ i:m.Tuple (n:=n+1),‖m.smear (m.back i) g‖≤C := by
  obtain ⟨b,hb,fee⟩:=TestBudget.bound_fin g
  let Z:Sample (n+1)→ℂ:=fun _=>1
  let F:Points (n+1)→ℂ:=fun _=>1
  have see:XSpace.Cirrus.Senses univ Z F:=fun _ _=>tendsto_const_nhds
  have pay:=graduate Z F isOpen_univ continuousOn_const (subset_univ (tsupport g)) g.hasCompactSupport see
    (fun _ _ _=>rfl) 1 zero_lt_one
  refine ⟨1+b+‖g.applyTo F‖,by positivity,?_⟩
  filter_upwards [pay] with m hm
  have hx:∀i:m.Tuple (n:=n+1),m.smear (m.back i) g=(‖m.smear (m.back i) g‖:ℂ):=by
    intro i
    obtain ⟨eq,nn⟩:=paid m (m.back i) g good
    rw [eq,Complex.norm_real,Real.norm_of_nonneg nn]
  have he:Deposit m Z g=((m.spacing^(4*(n+1))*∑ i:m.Tuple (n:=n+1),‖m.smear (m.back i) g‖:ℝ):ℂ):=by
    simp only [Deposit,Z,mul_one,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sum]
    congr 1;exact sum_congr rfl (fun i _=>hx i)
  have price:‖Deposit m Z g‖≤b+‖g.applyTo F‖:=by
    calc
      _≤‖Deposit m Z g-g.applyTo F‖+‖g.applyTo F‖:=by simpa only [dist_eq_norm,sub_zero] using dist_triangle (Deposit m Z g) (g.applyTo F) 0
      _≤_:=by linarith only [hm g Subset.rfl b fee]
  rw [he,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (pow_nonneg m.positive.le _)
    (sum_nonneg (fun _ _=>norm_nonneg _)))] at price
  linarith

/-- The signed all-mark closed Wilson perturbative reader, weighted by the
native finite far detector, versus the independently fixed MS pair/word at
the same relative scale. No assumption on an inverse ambient volume. -/
theorem measured {hG:G.Simple} (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (D:Fin (n+1)→Label B₀) (g:Test (n+1)) (good:∀z,(g z).im=0 ∧ 0≤(g z).re)
    (K:Set (Points (n+1))) (non:Nonempty K) (leg:K⊆conf (n+1)) (lies:tsupport g⊆K)
    {A δ:ℝ} (ha:0<A) (hd:0<δ) (size:∀z∈K,∀i,‖relative z i‖≤A)
    (split:∀z∈K,∀i l:Fin (n+1),i≠l→δ≤‖Fountain.metric z i-Fountain.metric z l‖)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀s:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      let err:=fun u:ℝ=>(T₀ c' j)^h*‖reading R Q D g c c' s u k j per-
        WilsonPhysicalExteriorMSQuadrature.quadrature (grid R c c' true s (j,per)) g
          (fun z=>MSExteriorDilation.moment M D (u+log (T₀ c' j)) (Fountain.metric z) k)‖
      err μ≤exp (-q*Λ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ j) := by
  have purchase:=WilsonPhysicalExteriorRichFarCells.physical R M Q (hG:=hG) rows D K non leg ha hd size split
    slow h₁ h₂ h₃ lo μ (q+1) k h
  obtain ⟨C,hC,count⟩:=total g good
  have census:=Filter.eventually_all.mpr (fun s:Bool=>all_later R ((front R hG slow h₁ h₂ h₃ lo true s).eventually count))
  have grow:∀ᶠ j:ℕ in atTop,C≤exp (Λ j):=(tendsto_exp_atTop.comp (Literal.lambda_leads R.family hG)).eventually_ge_atTop C
  filter_upwards [purchase,census,grow] with j hj ht big s per hp
  let m:=grid R c c' true s (j,per)
  let T:=T₀ c' j
  let τ:=log T
  have pos:0<T:=exp_pos _
  let E:=exp (-(q+1)*Λ j)
  have ep:0≤E:=(exp_pos _).le
  have arrive (u:ℝ) (use:∀v:Sample (n+1),v.F=m→familiar v∈K→
      T^h*‖MSExteriorDilation.power (MSExteriorDilation.weight D) τ*cell R Q D c s u k j per v-
      MSExteriorDilation.moment M D (u+τ) (Fountain.metric (familiar v)) k‖≤E) :
      T^h*‖reading R Q D g c c' s u k j per-WilsonPhysicalExteriorMSQuadrature.quadrature m g
        (fun z=>MSExteriorDilation.moment M D (u+τ) (Fountain.metric z) k)‖≤exp (-q*Λ j):=by
    let Y(v:Sample (n+1)):=MSExteriorDilation.power (MSExteriorDilation.weight D) τ*cell R Q D c s u k j per v
    let F:=independent M D (u+τ) k
    let v(i:m.Tuple (n:=n+1)):Sample (n+1):=⟨m,m.back i,0⟩
    have term (i:m.Tuple (n:=n+1)) :
        ‖m.smear (m.back i) g*(Y (v i)-F (v i))‖≤‖m.smear (m.back i) g‖*(E/T^h):=by
      by_cases zero:m.smear (m.back i) g=0
      · rw [zero,zero_mul,norm_zero,zero_mul]
      obtain ⟨o,inside⟩:=support zero
      let v':Sample (n+1):=⟨m,m.back i,o⟩
      have hvalid:familiar v'∈K:=lies inside
      have he:=use v' rfl hvalid
      rw [common M D (u+τ) k v' (leg hvalid)] at he
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply (le_div_iff₀ (pow_pos pos h)).mpr
      rw [mul_comm];exact he
    have eq:reading R Q D g c c' s u k j per-WilsonPhysicalExteriorMSQuadrature.quadrature m g
        (fun z=>MSExteriorDilation.moment M D (u+τ) (Fountain.metric z) k)=
        (m.spacing:ℂ)^(4*(n+1))*∑i:m.Tuple (n:=n+1),m.smear (m.back i) g*(Y (v i)-F (v i)):=by
      rw [drawn M D g m (u+τ) k]
      change (m.spacing:ℂ)^_ * _ - (m.spacing:ℂ)^_ * _=_
      rw [←mul_sub,←sum_sub_distrib];congr 1
      exact sum_congr rfl (fun i _=> (mul_sub ..).symm)
    rw [eq,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg m.positive.le]
    have bank:=ht s per hp
    change m.spacing^(4*(n+1))*∑i:m.Tuple (n:=n+1),‖m.smear (m.back i) g‖≤C at bank
    calc
      _≤T^h*(m.spacing^(4*(n+1))*∑i:m.Tuple (n:=n+1),‖m.smear (m.back i) g‖*(E/T^h)):=by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg pos.le _)
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg m.positive.le _)
        exact (norm_sum_le ..).trans (sum_le_sum (fun i _=>term i))
      _=(m.spacing^(4*(n+1))*∑i:m.Tuple (n:=n+1),‖m.smear (m.back i) g‖)*E:=by
        rw [←sum_mul];field_simp [pos.ne']
      _≤exp (Λ j)*E:=mul_le_mul_of_nonneg_right (bank.trans big) ep
      _=exp (-q*Λ j):=by dsimp only [E];rw [←Real.exp_add];congr 1;ring
  exact ⟨arrive μ (fun v hvm hK=>(hj s per hp v hvm hK).1),
    arrive (μ+R.family.S.scale j) (fun v hvm hK=>(hj s per hp v hvm hK).2)⟩

end YM.Integration.WilsonPhysicalExteriorRichFarDeposit
end
