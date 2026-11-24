import YM.Integration.FVA1Physical.Wilson.FieldRowSchedule

/-! The selected kinetic tower discharges the weighted stationary-coordinate
map estimate at every period. Its constants depend only on the stage data.
Those exact prices can be included in the common construction at launch. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Qlocal.Schedule
open RG Precision
variable {G:Gauge}

def mapThreshold (f:MapPrices→StageThreshold) : Goal G :=
  fun M D A F => selectedThreshold (f M.K) M D A F

theorem mapThreshold_obtainable (f:MapPrices→StageThreshold) :
    Obtainable (mapThreshold (G:=G) f) := by
  intro s T C z R E hdr
  exact selectedThreshold_obtainable (G:=G) (f (PhysicalNext.ThroughLaunch.bearing s T)) s T C z R E hdr

end YM.Qlocal.Schedule

namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push Push.Uniform MSbar.Midpoint MSbar.Tramp Bloch Laurent
open scoped Classical Topology BigOperators
variable {G:Gauge}

def railWidth (M:MapPrices) (P:Patch) : ℝ := (M.α P.J/P.L.val)/5
def railFee (G:Gauge) (M:MapPrices) (P:Patch) (s:ℕ) : ℝ :=
  let d:=railWidth M P
  shellS (townCost G) (tintCost G) (Alto.low d s) (1+tranche P (M.α P.J) (Alto.drift M P.J)) d

theorem selected_land (R:Run G) {N n j r:ℕ} (hj:j<N) (S:Scene R.family.path.levels n r)
    (F:Forest (R.family.path.levels.clock.op j n).ratio) (v:(R.family.path.levels.clock.op j n).Choices)
    (s:ℕ) {a:ℝ} (ha:0≤a) (small:a ≤ railWidth R.metals.K (R.family.path.levels.clock.op j n).patch) :
    let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
    Syrup (address A.F G) (Tramp.path A.S.ratio G) a s (poring A.F A.ρ) (railFee G R.metals.K A.S.patch s) := by
  intro A
  let L:=RunFormalChain.fromRun R
  let P:=A.S.patch
  let M:=R.metals.K
  let e:=M.α P.J
  let d:=railWidth M P
  have pos:0<e:=M.alpha_pos _
  have linear:0<d:=by dsimp only [d,railWidth]; positivity
  have reach:d+a+a+d+d ≤ e/P.L.val :=by change a≤d at small;dsimp only [d,railWidth,e] at *;linarith
  have funds:0≤Alto.drift M P.J:=(Alto.cone_pos ..).le
  have cost: A.M.strip e (Alto.drift M P.J) :=by
    have H:=((R.alloy.B.plan.costs N j hj).2.2.2 [] (Nat.zero_le _)).1
    simp only [advanceC,List.length_nil,add_zero,pow_one] at H
    apply Work.F08.strip_mono H le_rfl
    apply le_trans (div_le_div_of_nonneg_right (show M.Ω P.J ≤ Alto.drift M P.J by
       unfold Alto.drift; linarith only [le_abs_self (M.Ω P.J)]) (by positivity)) _
    exact div_le_self funds (Nat.one_le_cast.mpr P.L.property)
  have cc:Critical A.F A.pre.clip A.pre.path A.ρ :=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [L.clips N n (j+1) hj,L.selected N n (j+1) hj]
    exact (L.planned.critical N j n hj F).1
  have guessed:Guessed A.F (installed A.S.ratio A.M) A.ρ :=
    (L.planned.critical N j n hj F).2
  have poly:=Alto.low_earns d s linear
  apply bookF _ _ _ reach linear ha (zero_le_one.trans poly.1) linear.le
    (add_nonneg zero_le_one (funds0 A.M pos cost funds)) (fun t=>poly.2 t (Nat.cast_nonneg t))
  · exact stape A.F A.M A.pre.path A.pre.clip A.ρ cc guessed pos cost funds
  · exact Uniform.town A.F
  · exact cardP (S:=A.S) (G:=G)

end YM.Integration.FVA1Physical.Wilson
