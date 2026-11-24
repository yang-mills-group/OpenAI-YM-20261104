import YM.Integration.WilsonPositionScaleLawGuardNear

/-! One filed physical homogeneous order pays all its lower truncations uniformly on the same originals. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardDescent
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize Asymptotics
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionScaleLawGuardSheet (atValue)
open WilsonPositionScaleLawGuardInvoice (sheet)
open WilsonPositionScaleLawGuardPhysical (expected)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics Polynomial

theorem tail {A:Type*}[NormedRing A][NormedAlgebra ℂ A](a:PowerSeries A)(z:ℂ)(p k:ℕ){B:ℝ}(_hB:0≤B)
    (fees:∀j≤p+k,‖coeff j a‖≤B)(small:‖z‖≤1):
    ‖atValue (p+k) a z-atValue p a z‖≤(k:ℝ)*B*‖z‖^(p+1):=by
  induction k with
  | zero=>simp
  | succ k ih=>
    have base:=ih (fun j h=>fees j (by omega))
    have power:‖z‖^(p+k+1)≤‖z‖^(p+1):=pow_le_pow_of_le_one (norm_nonneg _) small (by omega)
    have next:‖z^(p+k+1) • coeff (p+k+1) a‖≤B*‖z‖^(p+1):=by
      rw [norm_smul,norm_pow,mul_comm B]
      exact mul_le_mul power (fees _ le_rfl) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    change ‖atValue (p+k+1) a z-atValue p a z‖≤_
    rw [WilsonPositionScaleLawGuardQuadratic.nextTerm,add_sub_right_comm]
    calc _≤_:=norm_add_le _ _
         _≤(k:ℝ)*B*‖z‖^(p+1)+B*‖z‖^(p+1):=add_le_add base next
         _=_:=by push_cast;ring

variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "gθ"=>kinetic Z F J
include H in
theorem original (funded:Coupling G (kinetic Z F J))(d:ℕ){p Q:ℕ}(h:p≤Q)(law:WilsonPositionScaleLawGuardLittle.scale F J Z M ν d Q):
    WilsonPositionScaleLawGuardLittle.scale F J Z M ν d p:=by
  let X:=(Bel R.family.book).Field d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le h
  let a(t:Ratio):=(sheet R.family Z M ν t d).homogeneous
  obtain ⟨B,hB,bounds⟩:=WilsonPositionScaleLawGuardBanks.bounded (p+k) (fun j t=>coeff j (a t)) (WilsonPositionScaleLawGuardBanks.homogeneous R.family Z M H ν d)
  let C:=(k:ℝ)*B
  have home:Tendsto (fun w:ℝ×Ratio=>gθ w.1) sweep (𝓝 0):=(funded.conforms hG).comp tendsto_fst
  have lim:Tendsto (fun w:ℝ×Ratio=>|gθ w.1|) sweep (𝓝 0):=by simpa only [abs_zero] using home.abs
  have cheap:∀ᶠw:ℝ×Ratio in sweep,|gθ w.1|≤1:=((tendsto_order.mp lim).2 1 one_pos).mono fun _ h=>h.le
  have shrink:Tendsto (fun w:ℝ×Ratio=>C*|gθ w.1|) sweep (𝓝 0):=by simpa only [mul_zero] using (tendsto_const_nhds (x:=C)).mul lim
  have first:(fun w:ℝ×Ratio=>dressed Z F J d w.1 w.2-expected F J Z M ν d (p+k) w.1 w.2)=o[sweep] (fun w=>gθ w.1^p):=by
    apply isLittleO_iff.mpr;intro ε hp
    filter_upwards [isLittleO_iff.mp law hp,cheap] with w full near
    exact full.trans (mul_le_mul_of_nonneg_left (by
      simp only [Real.norm_eq_abs,abs_pow]
      exact pow_le_pow_of_le_one (abs_nonneg _) near h) hp.le)
  have rest:(fun w:ℝ×Ratio=>expected F J Z M ν d (p+k) w.1 w.2-expected F J Z M ν d p w.1 w.2)=o[sweep] (fun w=>gθ w.1^p):=by
    apply isLittleO_iff.mpr;intro ε hp
    filter_upwards [cheap,(tendsto_order.mp shrink).2 ε hp] with w near cost
    have nz:‖(gθ w.1:ℂ)‖≤1:=by simpa only [Complex.norm_real,Real.norm_eq_abs] using near
    have invoice:=tail (a w.2) (gθ w.1:ℂ) p k hB (bounds w.2) nz
    rw [Complex.norm_real,Real.norm_eq_abs] at invoice
    calc _≤C*|gθ w.1|^(p+1):=invoice
         _=(C*|gθ w.1|)*|gθ w.1|^p:=by rw [pow_succ];ring
         _≤_:=by rw [Real.norm_eq_abs,abs_pow];exact mul_le_mul_of_nonneg_right cost.le (pow_nonneg (abs_nonneg _) _)
  apply (first.add rest).congr _ (fun _=>rfl)
  intro w;dsimp only;abel

end YM.Integration.WilsonPositionScaleLawGuardDescent
