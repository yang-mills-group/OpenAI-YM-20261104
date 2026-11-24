import YM.Integration.WilsonOriginalObservedRoseScaledWallet
import YM.Integration.WilsonOlderFreshSoftSocketStationPanelCapital

/-! The two finite physical bills on the same fitted columns. Depositing the terminal film spends its own finite constituent degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePooledFilms
open Function Filter Finset RG Lattice Wilson Source Labels PhysicalNext.Repeat.Legato
open WilsonOriginalObservedRoseMeshPurse (quote)
open WilsonOriginalObservedRoseMeshHeight (variation height tilt)
open WilsonOriginalObservedRoseScaledWallet (share)
open WilsonReceivedCanonicalVersePortfolio (Selection weight wallet nonneg)
open WilsonReceivedCanonicalVerseRegister (shoulder)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonThermometerPositionTunedSlope (Columns)
open PertExtension PertExtension.LatticePT ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)
local notation "C" => R.family
local notation "a" => R.family.S.a
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "F" i:max => R.family.labels.level (d i)

private theorem population (s:Finset (Fin n)){z:ℝ}(big:1≤z):share n z^(Fintype.card s)≤z:=by
  have card:(Fintype.card s:ℝ)≤(n:ℝ)+1:=by
    have h:s.card≤n:=by simpa using s.card_le_univ
    rw [Fintype.card_coe]
    exact_mod_cast (h.trans (Nat.le_succ n))
  have zp:=zero_lt_one.trans_le big
  unfold share
  rw [←Real.exp_nat_mul,←Real.exp_log zp]
  apply Real.exp_le_exp.mpr
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity:0<(n:ℝ)+1)).mpr
  simpa only [Real.log_exp,mul_comm (Real.log z)] using mul_le_mul_of_nonneg_right card (Real.log_nonneg big)

private theorem aggregate (s:Finset (Fin n))(M cost:Fin n→ℝ)(E:Fin n→ℕ)(A:ℕ){z h:ℝ}(big:1≤z)(hp:0≤h)
    (mp:∀i,0≤M i)(cp:∀i,0≤cost i)
    (due:∀i∈s,cost i≤M i*h^(E i)*z^(A*d i)*share n z):
    (∏i:s,cost i)≤(∏i:s,M i)*h^(∑i:s,E i)*z^(A*height d s+1):=by
  have acc:(∏i:s,cost i)≤∏i:s,M i*h^(E i)*z^(A*d i)*share n z:=
    prod_le_prod (fun i _=>cp i) (fun i _=>due i i.prop)
  apply acc.trans
  simp only [prod_mul_distrib,prod_const,card_univ,prod_pow_eq_pow_sum,←Finset.mul_sum,WilsonOriginalObservedRoseMeshHeight.height,pow_succ]
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_left (population s big)
    (mul_nonneg (mul_nonneg (prod_nonneg fun _ _=>mp _) (pow_nonneg hp _)) (pow_nonneg (zero_le_one.trans big) _))

theorem original (j:Fin n→ℕ)(N per K A:ℕ)(cut:K≤N)(Y w:∀i,(C).label (d i))
    (priced:∀i,(F i).coeffSize (w i)≤quote R d (tilt n A) (j i) K N per i (Y i))
    (M:Fin n→ℝ)(E:Fin n→ℕ)(positive:∀i,0≤M i)
    (wage:∀i,variation R d (j i) N per i (Y i)≤M i*(H K)^(E i))
    (s:Finset (Fin n)){z:ℝ}(big:1≤z)(mesh:∀i∈s,a (j i)/a K≤z^A):
    (∑q:Selection R d s,‖weight R d N per K w s q‖)≤wallet R d M s*(H K)^(∑i:s,E i)*z^(A*height d s+1) ∧
    (∑b:Columns R (fun i:s=>d i),‖packet R d s w N per K b‖)≤
      (∏i:s,M i)*(H K)^(∑i:s,(E i+WilsonOriginalPublicFigureIncome.height R (d i)))*z^(A*height d s+1):=by
  let h:=H K
  have hp:0≤h:=zero_le_one.trans (R.family.path.levels.fits.delayed K).le
  have zp:0≤z:=zero_le_one.trans big
  have sharep:0 ≤ share n z:=(Real.exp_pos _).le
  have column(i:Fin n)(inside:i∈s):(F i).coeffSize (w i)≤M i*h^(E i)*z^(A*d i)*share n z:=by
    have ap:0<(a (j i))^(d i):=pow_pos ((C).S.a_pos _) _
    have p:=WilsonOriginalObservedRoseScaledWallet.columns R d A (j i) K N per i (Y i) (w i)
      ((C).S.a_pos _) big (mesh i inside) (mesh i inside) (priced i) le_rfl
    apply (mul_le_mul_iff_of_pos_left ap).mp
    calc _≤_:=p
         _=(a (j i))^(d i)*(variation R d (j i) N per i (Y i)*z^(A*d i)*share n z):=by ring
         _≤_:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (wage i) (pow_nonneg zp _)) sharep) ap.le
  let bulk(i:Fin n):=∑q,shoulder R d i q
  have bp(i:Fin n):0≤bulk i:=sum_nonneg fun _ _=>nonneg R d i _
  have cp(i:Fin n):0≤(F i).coeffSize (w i):=sum_nonneg fun _ _=>norm_nonneg _
  constructor
  · apply (WilsonReceivedCanonicalVersePortfolio.priced R d N per K cut w s (fun i=>(F i).coeffSize (w i)) (fun _ _=>le_rfl)).trans
    apply aggregate d s (fun i=>bulk i*M i) (fun i=>bulk i*(F i).coeffSize (w i)) E A big hp
      (fun i=>mul_nonneg (bp i) (positive i)) (fun i=>mul_nonneg (bp i) (cp i))
    intro i hi
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (column i hi) (bp i)
  · let cost(i:Fin n):=∑b:(F i).Index,‖WilsonOriginalPublicTrialFigure.amount R d (regulatorRun (C) N per K)
        (fun j=>WilsonPositionProgramReportedField.entire R (d j) K (N,per) (w j)) i b‖
    change (∑b:Columns R (fun i:s=>d i),‖∏i:s,WilsonOriginalPublicTrialFigure.amount R d _ _ i (b i)‖)≤_
    simp only [norm_prod]
    rw [←Fintype.prod_sum (fun (i:s) (b:(F i.val).Index)=>‖WilsonOriginalPublicTrialFigure.amount R d (regulatorRun (C) N per K)
      (fun j=>WilsonPositionProgramReportedField.entire R (d j) K (N,per) (w j)) i.val b‖)]
    change (∏i:s,cost i)≤_
    apply aggregate d s M cost (fun i=>E i+WilsonOriginalPublicFigureIncome.height R (d i)) A big hp positive
      (fun _=>sum_nonneg fun _ _=>norm_nonneg _)
    intro i hi
    apply (WilsonOlderFreshSoftSocketStationPanelCapital.deposited R d (per:=per) cut w i).trans
    calc _≤(M i*h^(E i)*z^(A*d i)*share n z)*h^(WilsonOriginalPublicFigureIncome.height R (d i)):=
          mul_le_mul_of_nonneg_right (column i hi) (pow_nonneg hp _)
         _=_:=by rw [pow_add];ring

end YM.Integration.WilsonOriginalObservedRosePooledFilms
end
