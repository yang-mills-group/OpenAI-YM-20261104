import YM.Integration.WilsonCapturedPrimaryWardHome
import YM.Integration.WilsonCapturedPrimaryWardAppointment

/-! The raw equation mismatch of a genuine displaced compensated source and an original reference column. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardGapHome
open Function Filter Finset Lattice Wilson RG Labels Source Push Extraction RG12 RG17 Climb Trace.Pilot
open MergeProof Next.Extract PhysicalNext.Repeat.Legato PhysicalNext.Repeat Legato Bandage
open RG05Readout RG05Readout.Address WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open scoped Classical Topology
variable {G : Gauge} (R : Run G)

def gap {N p d : ℕ}
    (P : ∀ d, (ℕ × ℕ) → R.family.label d ≃ₗ[ℂ] R.family.label d) (x y:R.family.label d) :=
  (P d (N,p)).symm ((R.family.factory d N p).terminal.symm (x-y))

theorem inverse (d : ℕ) (ε : ℝ) (pos : 0<ε) : ∀ᶠ N : ℕ in atTop, ∀ p (x : R.family.label d),
    ‖(R.family.factory d N p).terminal.symm x‖ ≤ ‖x‖ * Real.exp (ε*R.family.S.scale N) := by
  filter_upwards [Work.D01.terminal_ball R.family R.makes d 1 ε pos] with N bound
  intro p x
  by_cases hx : x=0
  · simp [hx]
  let c : ℂ := ‖x‖
  have scalar : ‖c‖ = ‖x‖ := Complex.norm_real _ |>.trans (Real.norm_of_nonneg (norm_nonneg _))
  have nc : c≠0 := by simpa [c] using (norm_ne_zero_iff.mpr hx)
  let v:=c⁻¹ • x
  have one : ‖v‖=1 := by rw [show ‖v‖=‖c⁻¹‖*‖x‖ from norm_smul _ _,norm_inv,scalar,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have restore : c • v=x := by simp [v,smul_smul,nc]
  calc
    ‖(R.family.factory d N p).terminal.symm x‖ =
        ‖c‖*‖(R.family.factory d N p).terminal.symm v‖ := by
          conv_lhs => rw [←restore,map_smul,norm_smul]
    _ ≤ _ := by rw [scalar]; exact mul_le_mul_of_nonneg_left (bound p v one.le) (norm_nonneg _)

def column {d k N p : ℕ} (Q : Emblems R.family d) (h : k≤N) (y : Palette R.family d) :=
  (R.family.factory d N p).terminal (finer Q h y (primaryLetter d))

theorem price {E : ∀ d, SectionData (R.family.labels.level d)} {W : Push.Mark.Weave G}
    (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) {b : Presentation R.family}
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a)) (d : ℕ) (ε : ℝ) (pos : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ N : ℕ in atTop, ∀ p (h:k≤N) (sites : ∀ j,Bud R.family p j)
      (B : ℕ→ℕ→ℝ) (X : Sight R.family d p) (Q : Emblems R.family d),
      Enrolled R.makes R.doors B k N p d sites X Q → ∀ (x : R.family.label d) (y : Palette R.family d),
      (R.family.labels.level d).coeffSize (gap R P (N:=N) (p:=p) x (column R (p:=p) Q h y)) ≤
        2*(Fintype.card (R.family.labels.level d).Index * ‖x‖ + size y)*Real.exp (ε*R.family.S.scale N) := by
  obtain ⟨Z,Y,stamp⟩:=house.hearth d
  filter_upwards [string_paid (C:=R.family) pos] with k string
  filter_upwards [inverse R d ε pos,stamp.stamped] with N actual block
  intro p h sites B X Q list x y
  let F:=R.family.labels.level d
  let u : R.family.label d := (R.family.factory d N p).terminal.symm x
  let w:=finer Q h y
  let a : R.family.label d := w (primaryLetter d)
  let t:=Real.exp (ε*R.family.S.scale N)
  have main : F.coeffSize u ≤ Fintype.card F.Index * (‖x‖*t) := by
    calc
      _ ≤ ∑ _i : F.Index, ‖x‖*t := Finset.sum_le_sum fun i _=>(norm_le_pi_norm u i).trans (actual p x)
      _ = _ := by simp
  have secondary : F.coeffSize a ≤ size w := by
    rw [bill_group]
    exact Finset.single_le_sum (f:=fun j=>(R.family.labels.level (kept j)).coeffSize (w j))
      (fun _ _=>Work.G08.size_nonneg _ _) (Finset.mem_univ (primaryLetter d))
  have grows : size w ≤ t*size y := by
    apply (list.inverse le_rfl h le_rfl y).trans
    apply mul_le_mul_of_nonneg_right _ (size_ge _)
    apply (string N h).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_self _ (RG.Shoot.scale_nn R.family.path.levels k)) pos.le)
  have triangle : F.coeffSize (u-a) ≤ F.coeffSize u+F.coeffSize a := by
    simp only [Frame.coeffSize,←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _=>norm_sub_le _ _
  have eq : gap R P (N:=N) (p:=p) x (column R (p:=p) Q h y) = (P d (N,p)).symm (u-a) := by
    simp only [gap,column,u,a,w,map_sub,LinearEquiv.symm_apply_apply]
  rw [eq]
  calc
    _ ≤ 2*F.coeffSize (u-a) := (block p).2.1 _
    _ ≤ 2*(Fintype.card F.Index*(‖x‖*t)+t*size y) :=
      mul_le_mul_of_nonneg_left (triangle.trans (add_le_add main (secondary.trans grows))) (by norm_num)
    _ = _ := by ring

open WilsonCapturedPrimaryWardHome
open Ribbons
open private row read from YM.Integration.WilsonCapturedPrimaryWardHome

theorem original {E : ∀ d, SectionData (R.family.labels.level d)} {W : Push.Mark.Weave G}
    (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) {b : Presentation R.family}
    (simple : G.Simple) (portfolio : ∀ d,Push.Mark.Portfolio R.family.params (E d) (W d))
    (house : Hearthside R.family E W P b (Bandage.fly R.alloy.B.a)) (d : ℕ) :
    ∀ᶠ l:ℕ in atTop, ∀ᶠ k:ℕ in atTop, ∀ᶠ N:ℕ in atTop,
    ∀ p (h:l≤N) (sites:∀j,Bud R.family p j) (B:ℕ→ℕ→ℝ) (X:Sight R.family d p) (Q:Emblems R.family d),
      Enrolled R.makes R.doors B l N p d sites X Q →
      ∀ (x:R.family.label d) (y:Palette R.family d),
      BlockCost (Q:=R.family.S)
        (WilsonOffsetReportingProducts.residual R.family (E d) N p (P d (N,p)) (x-column R (p:=p) Q h y) 0)
        k (R.family.beta N p) (2*(Fintype.card (R.family.labels.level d).Index*‖x‖+size y)*
          Real.exp (-(1/64:ℝ)*R.family.S.scale N)) := by
  filter_upwards [price R P house d (1/64) (by norm_num)] with l issued
  filter_upwards [WilsonCapturedPrimaryWardHome.difference R simple portfolio house d] with k rows
  filter_upwards [rows,issued] with N home paid
  intro p h sites B X Q enrolled x y
  let v := column R (p:=p) Q h y
  have claim := home p (gap R (N:=N) (p:=p) P x v)
  have identity : row R (E d) (fun n q=>P d (n,q)) N p 0 (gap R (N:=N) (p:=p) P x v) =
      WilsonOffsetReportingProducts.residual R.family (E d) N p (P d (N,p)) (x-v) 0 := by
    change R.family.O N p ((R.family.factory d N p).terminal ((P d (N,p)) (gap R P x v))) 0 -
      Source.initial (E d) R.family.path N p (gap R P x v) 0 = _
    simp [gap,WilsonOffsetReportingProducts.residual,WilsonOffsetEquationLaw.incoming]
  rw [identity] at claim
  refine ⟨claim.stop,claim.safe,claim.amount.trans ?_⟩
  refine (mul_le_mul_of_nonneg_right (paid p h sites B X Q enrolled x y) (Real.exp_pos _).le).trans_eq ?_
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

end YM.Integration.WilsonCapturedPrimaryWardGapHome
