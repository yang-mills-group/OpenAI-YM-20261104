import YM.RGComparison01.AuxWeigh

/-! # Actual derivatives in the minimal moving collar. Normalize prior to interpolation. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxWeigh
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} {P : Teller G} {C Z u a v p H t E T₀ D : ℝ} {k j : ℕ}
  {c f : Side} {S:StepData c f} (F : Forest S.ratio) (T:Tube G S) (L:S.Choices) (A: ChartRatio G) (ρ: Bid.Dir G c→AxisChart G F)
  (B:BudgetPoint) (J : Config G f → ℝ) (β:ℝ)
local notation "M" => Pane.virgin T B β
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "V" => (fun x:Xs=> represent (tint G _ x))
local notation "U₁" => overall F T B β
variable (p' : Intake P T t (Pane.virgin T B β)) (hv : GaugeInvariant J) (hJ : Envelope J)
    (hH : ∀ i:Config G f, flags B.threshold i=∅→|J i|≤ T₀) (hT : 0 ≤ T₀)
    (hp : PaintSupply G j C) (he : Brush j E 1 Real.exp 0) (hh : 0≤ prime G S.kernel j C E β u) (hB : (Fintype.card (Bond c):ℝ)≤u)
local notation "K" => prime G S.kernel j C E β u
local notation "φ" => coverLog F T A L ρ β
include p' hv hJ hH hT hp he hh hB F
lemma above (x:Xs) (hx : ‖x‖<1): Brush j (T₀*K*tramp T B β x) 1 (weighed T B β J) x:= by
  let U y i := overall F T B β (V y) i
  let U' y i := U y i * J (F.drape i)
  have ha : S.patch.Branches S.kernel G:= p'.ready.knobs.symm ▸ p'.ready.kernel
  have he' y := stipend F T B β J p' hv hJ y; obtain ⟨d,hd⟩:= S.density_bound ha β; obtain ⟨e,he0⟩:= ((M).envelope p'.cap).cost
  have hU y i : U y i ≤ |d| * |e|:= by
    unfold U; rw [Fare.total]; apply mul_le_mul ((hd _ _).trans (le_abs_self _)) ((le_abs_self _).trans ((he0 _).trans (le_abs_self _))) _ (abs_nonneg _); rw [Pane.sparkling]; split <;> positivity
  have hK : 0≤T₀*K:=mul_nonneg hT hh
  have hy(y) (H:‖y‖<1) i : Brush j (T₀*K*U y i) 1 (fun y=> U' y i) y:= by
    have hg:= volumeQ F T B β i hp hB y H.le he
    by_cases H':flags B.threshold (F.drape i)=∅
    · have hp': ‖J (F.drape i)‖≤ T₀:= hH _ H'; rw [mul_assoc]; exact ((hg.smul (J (F.drape i))).climb (mul_le_mul_of_nonneg_right hp' hg.nonneg) le_rfl).shimmy (Eventually.of_forall fun i=>mul_comm _ _)
    have hz i': U i' i=0:= by unfold U; rw [Fare.total,Pane.sparkling,if_neg H',mul_zero]
    simp_rw [U',hz,zero_mul, mul_zero]; exact AuxCurtain.constant (u:=0) zero_le_one norm_zero.le
  have hf : Meristem U' x (F.order G) j := (Meristem.points _ _ ⟨fun _=> (T₀*K)*(|d| *|e|),integrable_const _, (continuous_norm.continuousAt.eventually (gt_mem_nhds hx)).mono fun y hi i=> (hy y hi i).climb (mul_le_mul_of_nonneg_left (hU y i) hK) le_rfl⟩ (Eventually.of_forall fun y=>(he' y).1.meas)).1
  have hw := amt F T B β _ P p' (V x)
  refine (hf.buds _ ((hw.1.integrable _).const_mul _) zero_le_one (le_of_eq ?_) (ae_of_all _ (fun i=> hy x hx i))).shimmy (Eventually.of_forall fun i=> (he' i).2)
  rw [MeasureTheory.integral_const_mul]; apply congr_arg; exact hw.2.symm

variable (hf : LocalRatio A) (h : Golf (Lapis.table F L T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ L) k D v v a) (hk : j≤ k)
local notation "P₀" => assay F T A ρ L β

def cutFee (j:ℕ) (W T Z p H E : ℝ):= let w:= oat j p H; W*T*Z*clump j (w+w) E*2^j
include hf h hk
lemma normalized (x:Xs) (hx : ‖x‖ < v) (ht : tramp T B β x≤ P₀ x * H) :
    Brush j (cutFee j K T₀ H a β E) 1 (rescale F T A ρ B L β J) x:= by
  have hβ : 0< β:= p'.positive; have hs:= sun F A β hβ hf; have hb: 0<P₀ x:= mul_pos hs (Real.exp_pos _)
  let p y:= φ y-φ x
  have hC:=octane F T A ρ β L hk hx h hβ
  let r:= oat j a β; let D:= clump j (r+r) E
  have hp' := composite hC (by rw [sub_self]; exact he)
  have hv : Brush j ((P₀ x)⁻¹ * D) 1 (fun y=>(P₀ y)⁻¹) x := by
    have h := hp'.smul ((P₀ x)⁻¹); rw [Real.norm_of_nonneg (by positivity)] at h
    apply h.shimmy; refine Eventually.of_forall fun i=>?_
    change (P₀ i)⁻¹=(P₀ x)⁻¹* Real.exp (p i); unfold assay p; rw [Real.exp_neg,Real.exp_neg,Real.exp_sub]; field_simp
  have hh := above F T B J β p' (by assumption) hJ hH hT hp he hh hB x (hx.trans_le h.small)
  apply ((AuxCurtain.together hh hv).climb _ le_rfl).shimmy (Eventually.of_forall (fun y=> div_eq_mul_inv _ _))
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ (2:ℝ)^j); apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (show 0≤T₀*K from mul_nonneg hT (by assumption))) hv.nonneg); apply le_of_eq; unfold D r; field_simp
end YM.RGComparison01.AuxWeigh
