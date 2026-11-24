import YM.Integration.WilsonPhysicalExteriorRichFarOrders

/-! The true deposited far-readout on the paid original Wilson cutoff, with
only its independently inspected outer mark compensated. Its actual inverse
returns each queried grade at its own power of T, uniformly on both tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarReturn
open Function Filter Set Finset Real MeasureTheory Lattice RG RG16 Pert Pert.Position
open XSpace XSpace.Cirrus FVA2 FVA2.Register MS MS.Land MS.Menus MS.Rake MS.Tone
open PhysicalNext.Repeat.Legato WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorQuadratureClock
open WilsonPhysicalExteriorRichFarGram WilsonPhysicalExteriorRichFarCells WilsonPhysicalExteriorRichFarFrame
open WilsonPhysicalExteriorFormalGram WilsonPhysicalExteriorRichFarOrders FVA2.O.Read
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (Q:Prescription (Press.portDeck G)) (H:ℕ)
local notation "B₀" => Press.portDeck G
local notation "I" => Glyph B₀ H
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

/-- Only the *exterior* glyph receives its field normalization in the actual
probe population. The other glyph is precisely the unknown output at zero. -/
def original (g:Test 2) (c c':ℝ) (s:Bool) (u:ℕ→ℝ) (z:Point):Matrix I I (PowerSeries ℂ):=fun a b=>
  PowerSeries.mk fun k=>Deposit (grid R c c' true s z)
    (fun v=>charge H (log (T₀ c' z.1)) b*cell R Q (word H a b) c s (u z.1) k z.1 z.2 v) g

private def priced {G:Gauge} (H:ℕ) (x:ℝ):Matrix (Glyph (Press.portDeck G) H) (Glyph (Press.portDeck G) H) (PowerSeries ℂ):=
  Matrix.diagonal (fun a=>PowerSeries.C (charge H x a))

def returned (g:Test 2) (c c':ℝ) (s:Bool) (u:ℕ→ℝ) (z:Point):Matrix I I (PowerSeries ℂ):=
  (series R Q H g c c' s u z)⁻¹*priced H (log (T₀ c' z.1))

private theorem swapped (x:ℝ):priced (G:=G) H x*priced H (-x)=1:=by
  rw [priced,priced,Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
  congr 1;funext a
  change PowerSeries.C (charge H x a)*PowerSeries.C (charge H (-x) a)=1
  rw [←map_mul]
  have factors:charge H x a*charge H (-x) a=1:=by
    unfold charge MSExteriorDilation.power
    norm_cast;rw [←Real.exp_add];simp
  rw [factors,map_one]

private theorem multiplier {n:ℕ} (m:Mesh)(f:Test n)(b:ℂ)(Y:Sample n→ℂ):
    Deposit m (fun v=>b*Y v) f=b*Deposit m Y f:=by
  let body:=fun i:m.Tuple=>(m.smear (m.back i) f)*Y ⟨m,m.back i,0⟩
  have eq:(∑i:m.Tuple,(m.smear (m.back i) f)*(b*Y ⟨m,m.back i,0⟩))=b*(∑i:m.Tuple,body i):=by
    rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;dsimp only [body];ring
  change (m.spacing:ℂ)^(4*n)*(∑i:m.Tuple,(m.smear (m.back i) f)*(b*Y ⟨m,m.back i,0⟩))=b*((m.spacing:ℂ)^(4*n)*(∑i:m.Tuple,body i))
  rw [eq];ring

theorem fields (g:Test 2) (c c':ℝ) (side:Bool) (u:ℕ→ℝ) (z:Point):
    original R Q H g c c' side u z=priced H (-log (T₀ c' z.1))*series R Q H g c c' side u z:=by
  apply Matrix.ext; intro a b
  apply PowerSeries.ext;intro k
  rw [original,PowerSeries.coeff_mk,priced,Matrix.diagonal_mul,PowerSeries.coeff_C_mul,
    series,PowerSeries.coeff_mk,gram,WilsonPhysicalExteriorRichFarDeposit.reading]
  let t:=log (T₀ c' z.1)
  let m:=grid R c c' true side z
  let Y:=cell R Q (word H a b) c side (u z.1) k z.1 z.2
  let D:=MSExteriorDilation.weight (word H a b)
  change Deposit m (fun v=>charge H t b*Y v) g=charge H (-t) a*Deposit m (fun v=>MSExteriorDilation.power D t*Y v) g
  rw [multiplier m g (charge H t b) Y,multiplier m g (MSExteriorDilation.power D t) Y]
  have factors:charge H t b=charge H (-t) a*MSExteriorDilation.power D t:=by
    have w:D=a.size+b.size:=by dsimp only [D];rw [MSExteriorDilation.weight,Fin.sum_univ_two];rfl
    rw [w]
    unfold charge MSExteriorDilation.power
    norm_cast
    rw [←Real.exp_add]
    congr 1;push_cast;ring
  exact (congrArg (fun q:ℂ=>q*Deposit m Y g) factors).trans (mul_assoc ..)

private theorem restore (g:Test 2)(c c':ℝ)(s:Bool)(u:ℕ→ℝ)(z:Point)
    (ht:IsUnit (Slate.slice 0 (series R Q H g c c' s u z))) :
    original R Q H g c c' s u z*returned R Q H g c c' s u z=1 ∧
    returned R Q H g c c' s u z*original R Q H g c c' s u z=1:=by
  let A:=series R Q H g c c' s u z
  have h: IsUnit A.det:=(Matrix.isUnit_iff_isUnit_det A).mp (Slate.lead ht rfl)
  have ab:=Matrix.mul_nonsing_inv A h
  have ba:=Matrix.nonsing_inv_mul A h
  have turns:=swapped (G:=G) H (log (T₀ c' z.1))
  have back:priced (G:=G) H (-log (T₀ c' z.1))*priced H (log (T₀ c' z.1))=1:=by
    simpa only [neg_neg] using swapped (G:=G) H (-log (T₀ c' z.1))
  rw [fields,returned]
  change (_*A)*(A⁻¹*_)=1 ∧ (A⁻¹*_)*(_*A)=1
  constructor
  · rw [mul_assoc,←mul_assoc A,ab,one_mul,back]
  · rw [mul_assoc,←mul_assoc (priced (G:=G) H _),turns,one_mul,ba]

private theorem charge_price (T:ℝ)(ht:0<T)(b:I):‖charge H (log T) b‖=T^b.size:=by
  rw [charge,MSExteriorDilation.power,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    Real.exp_nat_mul,Real.exp_log ht]

/-- The genuine R-rich far field has a two-sided inverse before all original
periods at the prescribed cutoff, on the whole finite bank simultaneously.
The price of column b is T to its own engineering dimension, independent of
perturbative order. -/
theorem measured {hG:G.Simple} (N:WilsonPrescription G) {S:Prescription B₀} {dial:Bool}
    (issued:Main.Match N hG M S dial) (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (g:Test 2) (good:∀z,(g z).im=0 ∧ 0≤(g z).re) (pop:Nonempty (tsupport g))
    (nondeg:IsUnit (MSSeparatedTestGram.matrix M H 0 0 g))
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (μ:ℝ) (P:ℕ) :
    ∃K:ℝ,0≤K ∧ ∃d:ℕ,∀ᶠ j:ℕ in atTop,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,∀s:Bool,
      let U:=original R Q H g c c' s (fun _=>μ) (j,per)
      let V:=returned R Q H g c c' s (fun _=>μ) (j,per)
      U*V=1 ∧ V*U=1 ∧ ∀k≤P,∀a b:I,‖PowerSeries.coeff k (V a b)‖≤
        K*(T₀ c' j)^b.size*(1+log (T₀ c' j))^d:=by
  let Idx:=Bool×Fin (P+1)×I×I
  let u:=fun _:ℕ=>μ
  have take:∀j,u j=μ ∨ u j=μ+R.family.S.scale j:=fun _=>Or.inl rfl
  choose C hC e fee using fun idx:Idx=>coefficients R M Q H N issued rows g good pop nondeg slow h₁ h₂ h₃ lo μ idx.1 u take idx.2.1.val idx.2.2.1 idx.2.2.2
  let bound:=∑i:Idx,C i
  let deg:=∑i:Idx,e i
  have pos:0≤bound:=Finset.sum_nonneg fun i _=>hC i
  have exp_le(i:Idx):e i≤deg:=Finset.single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (mem_univ i)
  have cost_le(i:Idx):C i≤bound:=Finset.single_le_sum (f:=C) (fun a _=>hC a) (mem_univ i)
  have live (s:Bool):∀ᶠ z in channel R c lo,IsUnit (Slate.slice 0 (series R Q H g c c' s u z)):=by
    obtain ⟨B,hB,h⟩:=tree R M Q H N issued rows g good pop nondeg slow h₁ h₂ h₃ lo μ s u take
    exact h.mono fun z wz=>wz.1
  have late:=WilsonPhysicalExteriorCompactWindow.recedes R hG slow h₁
  refine ⟨bound*(1+|μ|)^deg,mul_nonneg pos (by positivity),deg,?_⟩
  let enough:=fun z:Point=>∀s:Bool,
    let A:=original R Q H g c c' s u z
    let V:=returned R Q H g c c' s u z
    A*V=1 ∧ V*A=1 ∧ ∀k≤P,∀a b:I,‖PowerSeries.coeff k (V a b)‖≤
      (bound*(1+|μ|)^deg)*(T₀ c' z.1)^b.size*(1+log (T₀ c' z.1))^deg
  apply all_later (P:=enough) R
  filter_upwards [(Filter.eventually_all).mpr fee,(Filter.eventually_all).mpr live,
    (taking R c lo).eventually (late.eventually_ge_atTop 1)] with z paid hs hT
  intro s
  obtain ⟨ab,ba⟩:=restore R Q H g c c' s u z (hs s)
  refine ⟨ab,ba,?_⟩
  intro k hk a b
  let i:Idx:=(s,⟨k,by omega⟩,a,b)
  have one:1≤weight R c' u z:=by unfold weight;linarith only [abs_nonneg (u z.1+log (T₀ c' z.1))]
  have logt:0≤log (T₀ c' z.1):=log_nonneg hT
  have w: weight R c' u z≤(1+|μ|)*(1+log (T₀ c' z.1)) := MSExteriorFiniteScales.running_log μ _ logt
  have col:=charge_price (H:=H) (T₀ c' z.1) (zero_lt_one.trans_le hT) b
  simp only [returned,priced,Matrix.mul_diagonal,PowerSeries.coeff_mul_C,norm_mul,col]
  have base:‖Slate.slice k (series R Q H g c c' s u z)⁻¹ a b‖≤bound*((1+|μ|)*(1+log (T₀ c' z.1)))^deg:=
    (paid i).trans (mul_le_mul (cost_le i) ((pow_le_pow_right₀ one (exp_le i)).trans
      (pow_le_pow_left₀ (zero_le_one.trans one) w _)) (pow_nonneg (zero_le_one.trans one) _) pos)
  change ‖Slate.slice k (series R Q H g c c' s u z)⁻¹ a b‖*(T₀ c' z.1)^b.size≤_
  calc
    _ ≤ bound*((1+|μ|)*(1+log (T₀ c' z.1)))^deg*(T₀ c' z.1)^b.size :=
      mul_le_mul_of_nonneg_right base (pow_nonneg (zero_le_one.trans hT) _)
    _ = _ := by rw [mul_pow];ring

end YM.Integration.WilsonPhysicalExteriorRichFarReturn
end
