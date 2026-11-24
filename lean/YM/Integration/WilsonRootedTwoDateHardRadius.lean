import YM.Integration.QLocalThermalTokenTariff
import YM.Integration.WilsonRetainedRequestedBudget

/-! Shrinking every independently tested radius pays a full linear share
of the original marked and forced bills on their existing addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardRadius
open Function Finset Lattice Wilson RG Marker Overlay LocalComparison LocalComparison.Global
open Push.AbsoluteSums Comparison.Density.RenderM RG3.Script.Picnic
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {Γ:Census V}
    {D:V → ComparisonDensity.Address.Orbit} {p:BudgetPoint} {a:V→Support n}
    {Z:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n} {w:V→ℝ}

def smaller (t:ℝ) (w:V→ℝ) := fun v=>t*w v

theorem word (hw:∀v,0<w v) {t:ℝ} (ht:0<t) (hs:t≤1) (s:Γ.Mode) {v:V} (used:v∈s.val) :
    Poly.toll (smaller t w) s ≤ t*Poly.toll w s := by
  have count:1 ≤ s.val.card:=Finset.card_pos.mpr ⟨v,used⟩
  have shrink:t^s.val.card ≤ t:=by simpa only [pow_one] using pow_le_pow_of_le_one ht.le hs count
  simpa only [smaller,Poly.toll,Finset.prod_mul_distrib,Finset.prod_const]
    using mul_le_mul_of_nonneg_right shrink (Poly.worth hw s).le

theorem packets (M:MarkedPackets D G n Γ) {g width bill:ℝ} {off cov:ℕ}
    (H:M.Paid p a Z w g width bill off cov) {t:ℝ} (ht:0<t) (hs:t≤1) :
    M.Paid p a Z (smaller t w) g width (t*bill) off cov := by
  refine { H with positive:=fun v=>mul_pos ht (H.positive v), roots:=?_ }
  intro v
  apply budget_mono (budget_scale ht.le (H.roots v))
  · intro i
    split_ifs with seen
    · cases e:M.packet i with
      | none=>exact le_rfl
      | some T=>exact mul_nonneg (mul_nonneg (mul_nonneg (Poly.worth (fun v=>mul_pos ht (H.positive v)) _).le
           (norm_nonneg _)) (H.coefficient i T e).1) (Real.exp_pos _).le
    exact le_rfl
  · intro i
    by_cases seen:v∈(M.mode i).val
    · simp only [seen,if_true]
      cases e:M.packet i with
      | none=>simp
      | some T=>
        calc
          _ ≤ (t*Poly.toll w (M.mode i))*‖(g:ℂ)^M.power i‖*T.coin*Real.exp (width*T.fall):=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (word H.positive ht hs _ seen) (norm_nonneg _)) (H.coefficient i T e).1) (Real.exp_pos _).le
          _ = _:=by ring
    · simp only [seen,if_false,mul_zero,le_refl]

def compulsory {X:Type} {P:Rep G n} {o:V→Site n} (T:Taste X o P Γ) {κ b:ℝ}
    (h:ForcedBudget p T w κ b) (hw:∀v,0<w v) {t:ℝ} (ht:0<t) (hs:t≤1) :
    ForcedBudget p T (smaller t w) κ (t*b) := by
  refine {black:=h.black,black_nonnegative:=h.black_nonnegative,forced:=h.forced,total:=?_}
  intro v
  rw [show κ*(t*b)=t*(κ*b) by ring]
  apply budget_mono (budget_scale ht.le (h.total v))
  · intro i
    split_ifs
    · exact mul_nonneg (Poly.worth (fun v=>mul_pos ht (hw v)) _).le ((h.black_nonnegative i).trans (p.loMass _ _ (h.black_nonnegative i)))
    exact le_rfl
  · intro i
    split_ifs with seen
    · calc _ ≤ (t*Poly.toll w (T.menu.marks i.1 i.2))*p.mass (P.activities.forced i.1).support (h.black i):=
             mul_le_mul_of_nonneg_right (word hw ht hs _ seen) ((h.black_nonnegative i).trans (p.loMass _ _ (h.black_nonnegative i)))
           _ = _:=by ring
    · simp

theorem share (a b:ℝ) {σ:ℝ} (hσ:0<σ) : ∃t:ℝ,0<t ∧ t≤1 ∧ t*a≤σ/2 ∧ t*b≤1 := by
  let e:=min 1 (σ/2)
  let C:=1+max a 0+max b 0
  have he:0<e:=lt_min zero_lt_one (half_pos hσ)
  have ca:0 ≤ max a 0:=le_max_right _ _
  have cb:0 ≤ max b 0:=le_max_right _ _
  have hc:1 ≤ C:=by dsimp [C];linarith
  have cp:0<C:=zero_lt_one.trans_le hc
  have bill:(e/C)*C=e:=div_mul_cancel₀ _ cp.ne'
  refine ⟨e/C,div_pos he cp,(div_le_one cp).mpr ((min_le_left 1 (σ/2)).trans hc),?_,?_⟩
  · calc _ ≤ (e/C)*C:=mul_le_mul_of_nonneg_left (by dsimp [C];linarith [le_max_left a 0]) (div_pos he cp).le
         _ ≤ σ/2:=bill.trans_le (min_le_right _ _)
  · calc _ ≤ (e/C)*C:=mul_le_mul_of_nonneg_left (by dsimp [C];linarith [le_max_left b 0]) (div_pos he cp).le
         _ ≤ 1:=bill.trans_le (min_le_left _ _)

/-- Both parts of the ordered fusion bill at the same positive radius. -/
theorem margins {k b Q σ : ℝ} (B v κ : ℝ) (hσ : 0<σ) (reserve : 2*k*B≤σ) :
    ∃s : ℝ,0<s ∧ s≤1 ∧ 2*(k+v*(κ*(s*b)))*B≤3*σ/2 ∧ s*Q≤1 := by
  obtain ⟨s,p,u,a,c⟩ := share (2*v*(κ*b)*B) Q hσ
  refine ⟨s,p,u,?_,c⟩
  linarith only [reserve,show 2*v*(κ*(s*b))*B≤σ/2 by convert a using 1; ring,
    show 2*(k+v*(κ*(s*b)))*B=2*k*B+2*v*(κ*(s*b))*B by ring]

end YM.Integration.WilsonRootedTwoDateHardRadius
end
