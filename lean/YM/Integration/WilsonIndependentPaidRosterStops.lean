import YM.Integration.WilsonIndependentReportedCell

/-! One numerical comparison on the enrolled raw roster before its eligible
stopping page is selected. The three spatial errors remain on that same page. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPaidRosterStops
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Taping
open RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open WilsonIndependentRawRosterWord WilsonIndependentRawWordGeometry
open scoped Classical ENNReal NNReal

variable {G:Gauge}{I J:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)
    {M:J → ℕ}{n:Page M → Side}{S:Heir n G}(T:S.Accounts)
    (sites:J → I → Cover)

variable {T}{V:Reel S}{Γ:Flap M → Layer (Foot G) (Foot G)}{B:Flap M → Bride G}
    {L:Meter J}{cash:Flap M → ℝ≥0∞}{p f u:ℕ}{D:Choice M}{γ c₀:ℝ}
    (A:Cylinder V T Γ B L cash p f u)(lamp:Lantern S D L cash γ)(endings:V.Endings L)
    (sample:J → Sample 2)(x:J → Room)
    (start:∀w,S.l (Page.opening M w)=1)(clock:∀w,V.clock (Page.opening M w)=Clocks.flat)
    (same:∀w,TopF n w=(sample w).F.p.side)
    (fare:∀w,ENNReal.ofReal (1+WilsonIndependentRawRosterBudget.span (x w) (sites w) arms) ≤ L.val w)
    (clear:0<c₀)(safe:S.cushion c₀ x)
include A lamp endings start clock same fare clear safe


theorem original (q:ℕ)(hq:q ≤ p):
    ∃C:ℝ,0 ≤ C ∧ ∃k:ℕ,∀(stop:Choice M),D.age ≤ stop.age → ∀w,
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (film R W σ d key (sample w) (sites w) arms))-
        (note ((WilsonIndependentRawRosterOrbit.report R W σ d key arms T sites).main (stop.choose w) q 0):ℂ)‖ ≤
      C*(L.val w).toReal^k*S.modifyErr 0 f γ stop w:=by
  classical
  let Allowed(w:J):= {t:Fin (M w+1) // D.age w ≤ (t:ℕ)}
  letI(w:J):Nonempty (Allowed w):=⟨⟨⟨D.age w,Nat.lt_succ_of_le (D.young w)⟩,le_rfl⟩⟩
  let choose (s:∀w,Allowed w):Choice M:=⟨fun w=>(s w).1.val,fun w=>Nat.le_of_lt_succ (s w).1.isLt⟩
  let age(w:J)(t:Allowed w):Page M:=⟨w,t.1.val,Nat.le_of_lt_succ t.1.isLt⟩
  let cost(w:J)(t:Allowed w):ℝ:=S.transferErr 0 f γ w+(S.l (age w t)^γ)⁻¹
  let fee(w:J)(t:Allowed w):ℝ:=‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
    (film R W σ d key (sample w) (sites w) arms))-
    (note ((WilsonIndependentRawRosterOrbit.report R W σ d key arms T sites).main (age w t) q 0):ℂ)‖
  have bill(w:J)(t:Allowed w):0<cost w t:=add_pos (S.transfer_pos w) (inv_pos.mpr (Real.rpow_pos_of_pos (S.hl _) γ))
  have issued (s:∀w,Allowed w):∃C:ℝ,0 ≤ C ∧ ∃k:ℕ,∀w,fee w (s w)/cost w (s w) ≤ C*(L.val w).toReal^k:=by
    obtain ⟨C,k,hC,money⟩:=WilsonIndependentRawRosterOrbit.stopped R W σ d key arms sites A lamp endings
      sample x start clock same fare clear safe q hq (choose s) (fun w=>(s w).2)
    exact ⟨C,hC,k,fun w=>(div_le_iff₀ (bill w (s w))).mpr (money w)⟩
  obtain ⟨C,hC,k,money⟩:=WilsonIndependentReportedCell.uniform (Cell:=Allowed) (fun w t=>fee w t/cost w t)
    (fun C k w=>C*(L.val w).toReal^k) issued
  refine ⟨C,hC,k,fun stop h w=>?_⟩
  let t:Allowed w:=⟨⟨stop.age w,Nat.lt_succ_of_le (stop.young w)⟩,h w⟩
  exact (div_le_iff₀ (bill w t)).mp (money w t)

end YM.Integration.WilsonIndependentPaidRosterStops
