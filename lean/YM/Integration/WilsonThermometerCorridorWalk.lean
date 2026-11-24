import YM.Integration.WilsonThermometerCorridorRoster
import YM.Integration.WilsonThermometerCorridorCharge
import YM.Integration.WilsonThermometerMarchFaceTransport

/- Carry one earned joint original polynomial over each intervening physical
   edge. The chosen radius is kept in the conclusion so the terminal grouping
   acts on this same measured board and all its existing supported entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorWalk
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open RG05Readout.Pantry WilsonThermometerMixedBooked
open scoped Topology BigOperators Classical
open Planned.GuardedAtom Guard MergeProof.Accent MergeProof.Ribbon MergeProof.Menu PhysicalNext.Repeat.Mallow
set_option quotPrecheck false
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C"=> R.family
local notation "A"=> R.family.path.levels
local notation "β"=> (A).clock.hatBeta
local notation "V"=> Unit×I
local notation "Y"=> Stock.census (Unit×I)

omit [Fintype I] [DecidableEq I] in
theorem modest {w:V→ℝ}(j:ℕ)(i:V)(pos:0<w i):
    0<nextRadius R j w i ∧ nextRadius R j w i≤w i:=by
  have hot:=((A).fits.delayed (j+1)).le
  have positive:0<β (j+1):=zero_lt_one.trans_le hot
  have equal:renal (A) j=((β (j+1))^2)⁻¹:=by
    unfold renal probe
    rw [Real.rpow_neg positive.le]
    norm_num
  have ηpos:0<renal (A) j:=by rw [equal];positivity
  have η:renal (A) j≤1:=by
    rw [equal];exact inv_le_one_of_one_le₀ (one_le_pow₀ hot)
  have z:=Real.exp_pos (((A).budget j).supportExponent+1/2)
  have one:1≤Real.exp (((A).budget j).supportExponent+1/2):=Real.one_le_exp (by linarith [((A).budget j).exponent_pos])
  unfold nextRadius
  constructor
  · exact div_pos (mul_pos ηpos (mul_pos ηpos pos)) z
  · apply (div_le_iff₀ z).mpr
    exact (mul_le_of_le_one_left (mul_nonneg ηpos.le pos.le) η).trans
      ((mul_le_of_le_one_left pos.le η).trans (le_mul_of_one_le_right pos.le one))

theorem original (simple:G.Simple)(cater:Cater (C) R.doors)
    {b f N p:ℕ}(first:0<b)(fn:f≤N)
    (raw:∀j, V→Three G ((C).side j p))(o:∀j,V→Site ((C).side j p))
    (cost:ℕ→V→ℝ)(w:V→ℝ)(F:Config G ((C).side f p)→Poly (Y))
    (top:MenuBoard ((C).path.rep N p f) (raw f) F (o f) w (((A).budget f).supportExponent-2) 1)
    (pos:∀i,0<w i) (same:∀j,b≤j → j<f → o j=((A).clock.op j p).ratio.parent ∘ o (j+1))
    (rides:∀j,b≤j → ∀jf:j<f,∀i,Ride ((A).clock.op j p) (o (j+1) i) (o j i)
      (R.doors N p j (jf.trans_le fn)) 1 (raw (j+1) i) (raw j i) (cost j i))
    (load:∀j,b≤j → j<f → Occupancy (o (j+1)) (apron (A) j) ∧ Occupancy (o j) (apron (A) j))
    (cash:∀j,b≤j → j<f → ∀i,0≤cost j i ∧ 2*w i*cost j i≤1):
    ∀j,b≤j → ∀jf:j≤f,∃wallet:V→ℝ,
      (∀i,0<wallet i ∧ wallet i≤w i ∧ (wallet i)⁻¹≤(β f)^(6*(f-j))*(w i)⁻¹) ∧
      MenuBoard ((C).path.rep N p j) (raw j) (gust (C).path N p f F j jf) (o j) wallet
        (((A).budget j).supportExponent-2) 1:=by
  intro j bj jf
  induction jf using Nat.decreasingInduction with
  | self=>
    refine ⟨w,fun i=>⟨pos i,le_rfl,by simp⟩,?_⟩
    simpa only [gust_base] using top
  | of_succ j jf ih=>
    obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
    let j:=k+1
    obtain ⟨v,bill,board⟩:=ih (bj.trans j.le_succ)
    have spend (i:V):2*v i*cost j i≤1:=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bill i).2.1 (by norm_num)) (cash j bj jf i).1).trans (cash j bj jf i).2
    have edges: j<N:=jf.trans_le fn
    have act:=WilsonThermometerMixedBooked.original (I:=I) R cater (p:=p) (j:=k)
      edges (((A).budget (j+1)).supportExponent-2)
    dsimp only at act
    have carry:=act (raw (j+1)) (raw j) (o (j+1)) v (cost j) _ board (by linarith)
      (fun i=>(bill i).1) (fun i=>by have step:=rides j bj jf i; rw [same j bj jf,Function.comp_apply] at step; exact step)
      (load j bj jf).1 (by rw [←same j bj jf];exact (load j bj jf).2) spend
    refine ⟨nextRadius R j v,?_,?_⟩
    · intro i
      have cap:=modest R j i (bill i).1
      refine ⟨cap.1,cap.2.trans (bill i).2.1,(carry.2 i).trans ?_⟩
      have years:=ActualCoarseStagePrice.hatBeta_mono (A) simple (show j+1≤f from jf)
      calc β (j+1)^6 * (v i)⁻¹ ≤ β f^6 * ((β f)^(6*(f-(j+1)))*(w i)⁻¹):=
              mul_le_mul (pow_le_pow_left₀ (WardBin.hot _ _).le years _) (bill i).2.2
                (inv_nonneg.mpr (bill i).1.le) (pow_nonneg (WardBin.hot _ _).le _)
        _ = _:=by rw [←mul_assoc,←pow_add,show 6+6*(f-(j+1))=6*(f-j) by omega]
    · rw [gust_step _ _ _ _ _ jf,same j bj jf]
      exact carry.1
end YM.Integration.WilsonThermometerCorridorWalk
end
