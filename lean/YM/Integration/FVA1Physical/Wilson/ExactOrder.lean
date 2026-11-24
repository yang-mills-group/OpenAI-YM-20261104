import YM.Integration.FVA1Physical.Wilson.FieldRows
import YM.Integration.FVA1Physical.Wilson.TiltStencil

/-! The auxiliary tag of order p+1 computes the normalized insertion.
Only the first p incoming action and insertion coefficients affect the answer.
In particular the auxiliary tag never demands a higher-order physical scene. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {σ ι:Type} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
private theorem wick_prefix {p:ℕ} {f g:PowerSeries (Pot σ)} (same:Lap p f g) :
    Lap p (wickSeries f) (wickSeries g) := by
  intro n hn
  simp only [wickSeries,PowerSeries.coeff_mk,same n hn]

omit [DecidableEq σ] in
theorem tilted_prefix {p:ℕ} {f g u v :PowerSeries (Pot σ)} (hk:Kind f) (hg:Kind g)
    (h:Lap p f g) (hs:Lap p u v) : Lap p (tiltedStencil f u) (tiltedStencil g v) := by
  let N:=wickSeries (Spring f)
  let M:=wickSeries (Spring g)
  let X:=tiltedStencil f u
  let Y:=tiltedStencil g v
  have eqd:Lap p N M:=wick_prefix h.boots
  have eqn:Lap p (X*N) (Y*M):=by
    rw [show X*N=wickSeries (u*Spring f) from tiltedStencil_clear _ _ hk,
      show Y*M=wickSeries (v*Spring g) from tiltedStencil_clear _ _ hg]
    exact wick_prefix (hs.rises h.boots)
  have yy:Lap p (Y*N) (Y*M):=(show Lap p Y Y from fun _ _=>rfl).rises eqd
  have xy:Lap p (X*N) (Y*N):=fun j hj=>(eqn j hj).trans (yy j hj).symm
  let d:=PowerSeries.invOfUnit N 1
  have unit : d*N=1:=by
    apply PowerSeries.invOfUnit_mul
    rw [←PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [N,wickSeries,PowerSeries.coeff_mk,covers hk,wickStencil_one]
    rfl
  have e:=xy.rises (show Lap p d d from fun _ _=>rfl)
  simpa only [mul_assoc, show N*d=1 from (mul_comm N d).trans unit,mul_one] using e

theorem grow_prefix [Fintype ι] [DecidableEq ι] {p r t:ℕ}
    (V:Matrix σ ι ℝ) {C:Matrix ι ι ℝ} (pos:C.PosDef)
    {f g u v:PowerSeries (Pot σ)} (hk:Kind f) (hg:Kind g) (h:Lap p f g) (hs:Lap p u v)
    (hr:p<r) (ht:p<t) : Lap p (growP f u (V*C*V.transpose) r) (growP g v (V*C*V.transpose) t) := by
  intro i hi
  apply MvPolynomial.funext
  intro x
  exact (tiltedStencil_eq_grow V x pos f u hk r i (hi.trans_lt hr)).symm.trans
    ((congrArg (MvPolynomial.eval (parameters x (V*C*V.transpose))) (tilted_prefix hk hg h hs i hi)).trans
    (tiltedStencil_eq_grow V x pos g v hg t i (hi.trans_lt ht)))

def cropAction {τ:Type} (p:ℕ) (A:PowerSeries (Pot τ)) : PowerSeries (Pot τ) :=
  PowerSeries.mk fun i=>if i≤p then PowerSeries.coeff i A else 0

def cropIssue (A:Issue G) (p:ℕ) : Issue G := {A with T:=cropAction p A.T}

theorem crop_action_prefix (A:Issue G) (χ:ChartRatio G) (p:ℕ) (src:PowerSeries (Pot (Joint A.F G)))
    (kind:Kind A.T) (pd:(mold A.pre A.F A.v).PosDef) :
    Lap p (normalizedRows A χ src p) (normalizedRows (cropIssue A p) χ src p) := by
  have isKind:Kind (cropAction p A.T):=by
    unfold Kind at kind ⊢
    simpa only [cropAction,PowerSeries.coeff_mk,zero_le,if_true] using kind
  apply grow_prefix (straight A.F G) pd.inv (well A.F A.v χ _ kind) (well A.F A.v χ _ isKind)
      _ (fun _ _=>rfl) (Nat.lt_succ_self p) (Nat.lt_succ_self p)
  intro i hi
  simp only [barbed,map_add,PowerSeries.coeff_map,cropAction,PowerSeries.coeff_mk,if_pos hi]

private theorem crop_profile (A:Issue G) {n d:ℕ} (h:Expanse A.T 1 n) : Expanse (cropAction n A.T) 1 d := by
  constructor
  intro i _
  by_cases hi:i≤n
  · simpa only [cropAction,PowerSeries.coeff_mk,if_pos hi] using h.profile i hi
  simp [cropAction,hi]

private theorem crop_wedge (A:Issue G) {n d s:ℕ} {x a:ℝ} (hx:0<x)
    (h:Alto.Wedge A.T Alto.Dean x a s n) : Alto.Wedge (cropAction n A.T) Alto.Dean x a s d := by
  constructor
  intro i _
  by_cases hi:i≤n
  · simpa only [cropAction,PowerSeries.coeff_mk,if_pos hi] using h.shares i hi
  simp only [cropAction,PowerSeries.coeff_mk,if_neg hi]
  exact (show MvPolynomial.C (0:ℝ)=0 from map_zero _) ▸
    (Tin.constant hx 0 (show 0≤Alto.purse Alto.Dean x i from pow_nonneg hx.le _))

theorem same_order_field_rows {κ:Type} [Fintype κ] (I:κ→Lamp G)
    (J:Voice G) (clear:Clear G J) (χ:ChartRatio G) (hχ:LocalRatio χ) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G) (p s q L:ℕ)
    (part:Bool) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Issue G) (b:Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (z:Positions (Primary A.c G)), ‖z‖ ≤ A.fClock*D → ∀ (o:κ→Site A.f),
      (∀ j:Slice I, separation b (legs I o j).1 ≤ L*closeN y) →
      ∀ i ≤ p, Vault (address A.F G) {b} (αm y) s q (bulkPoint A z)
        (PowerSeries.coeff i (normalizedRows A χ (jointFieldBank I A o part) p)) (y^η) := by
  obtain ⟨t,buy⟩:=purchased_chart_chance J clear simple H H' P K branch hD 0
  obtain ⟨_,_,theater⟩:=waiting t H H' J χ hχ clear P 3 0
  filter_upwards [physical_field_rows I J clear χ hχ simple H H' P K branch p s q L part hD hη,
    buy,theater,(Alto.broad.comp (Work.E09.betaF_growth G P.L)).eventually_gt_atTop 0] with x offer paid hall positive
  intro A b patch kernel season y kind plane wedge z hz o near i hi
  obtain ⟨grants,cal,_,_⟩:=paid A patch kernel season z b hz
  have suite:=(hall.enter _ _ patch season (boxX y b) (boxY y b) A.F z A.v grants
    (by rw [patch]; exact cal.first)).2
  let Ac:=cropIssue A p
  have ckind:Kind Ac.T:=by
    unfold Kind at kind
    change PowerSeries.coeff 0 (cropAction p A.T)=0
    simpa only [cropAction,PowerSeries.coeff_mk,zero_le,if_true] using kind
  have eqn:=crop_action_prefix A χ p (jointFieldBank I A o part) kind suite.positivity i hi
  rw [eqn]
  exact offer Ac b patch kernel season ckind (crop_profile A plane) (crop_wedge A positive wedge) z hz o near i hi

end YM.Integration.FVA1Physical.Wilson
