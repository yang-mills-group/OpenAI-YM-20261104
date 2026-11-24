import YM.Integration.WilsonConditionalTaylorWheelRawColor
import YM.Integration.WilsonConditionalTaylorWheelClock
import YM.Integration.WilsonConditionalTaylorFieldBalance
import YM.Integration.WilsonConditionalTaylorWheelRealmLedger

/-! Extract the signed native kinetic counterterm and rebook all
retained occupied kernels in the original graded coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelBookedCoil
open Function Filter Lattice Laurent RG Wilson Exterior Precision Tree Bloch Next.Foundations PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos PhysicalNext.Repeat.Legato
open Next.Free FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof Lotus Mesa
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem signed (u:G.ColorIndex) (X:Cork.Slopes G):Cork.value u (-X) = -Cork.value u X:=by
  simp only [Cork.value,Cork.mir,Cork.net,Cork.hem,Pi.neg_apply,neg_mul,tsum_neg]

theorem stamp {I:Type} {E:ℕ} {A B H U:PowerSeries ℝ}
    (forward:Through E A H) (inverse:Through E B U)
    (P T:OrbitV I) (e r:ℕ) (cap:e≤E) (old:∀i≤e,-P i r=T i r):
    -Wine.stamp A B P e r=Wine.stamp H U T e r:=by
  rw [Wine.stamp,Wine.stamp,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have within:i≤e:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
  have scalars:=((forward.pow i).mul (inverse.pow r)) (e-i) (by omega)
  rw [Wine.bill,Wine.bill,scalars,←smul_neg,old i within]

variable (R:Run G) (u:G.ColorIndex) (N j:ℕ)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun k:ℕ=>Flat.routes (R.family.path.levels.clock.op k 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun k:ℕ=>(R.family.path.levels.blocks k 0).branches)
local notation "W" => Dove.model V wood b R.metals.O u N (j+1)
local notation "P" => destination V N j
local notation "incoming" => freshet V R.metals.O N j
local notation "raw" => FormalBulk08.Bank.waken P (wood j) W R.metals.O (b j)
local notation "H" => pitch V R.metals.O N j
local notation "C" => Wine.scalar u raw

theorem books (live:j<N) (E:ℕ) (fee:WilsonConditionalTaylorWheelRealmLedger.At R E j)
    (rows:∀e≤E,-incoming e 2=raw e 2):
    Through E H C ∧ Through E (Wine.bookH H) (Wine.bookH C) ∧ Through E (Wine.bookU H) (Wine.bookU C):=by
  obtain ⟨_,_,_,Q,_,levels,scheme,_⟩:=fee 0 (Nat.zero_le _) 0 (by omega)
  have read(e:ℕ):coeff e H= -Cork.value u (incoming e 2):=by
    have h:=WilsonConditionalTaylorWheelRawColor.original Q N j live e u
    rwa [levels,scheme] at h
  have equal:Through E H C:=by
    intro e he
    rw [read,Wine.scalar,coeff_mk,←rows e he,signed]
  have unit:Wine.Fresh H:=by
    rw [Wine.Fresh,coeff_zero_eq_constantCoeff_apply]
    have test:=angle_tilt (A:=Q.draws) Q.hG Q.green (N:=N) (m:=j) live
    rwa [levels,scheme] at test
  exact ⟨equal,WilsonConditionalTaylorFieldBalance.clocks unit ((equal 0 (Nat.zero_le E)).symm.trans unit) equal⟩

theorem original (live:j<N) (E:ℕ) (fee:WilsonConditionalTaylorWheelRealmLedger.At R E j)
    (rows:∀e≤E,∀r<E+2,-incoming e (r+1)=raw e (r+1)) (e r:ℕ) (cap:e≤E) (rank:r<E+2):
    -actionW V R.metals.O N j e (r+1)=Dove.model V wood b R.metals.O u N j e (r+1):=by
  obtain ⟨_,_,_,Q,_,levels,scheme,_⟩:=fee 0 (Nat.zero_le _) 0 (by omega)
  have pub:=WilsonConditionalTaylorWheelClock.onRealm Q N j live
  rw [levels,scheme] at pub
  have pair:=books R u N j live E fee (fun d hd=>rows d hd 1 (by omega))
  rw [conduct V R.metals.O live,pub.2.2,Dove.through V wood b R.metals.O u N j live]
  apply stamp pair.2.1 pair.2.2 (lop incoming) raw e (r+1) cap
  intro i hi
  simpa only [lop,if_neg (Nat.succ_ne_zero r)] using rows i (hi.trans cap) r rank

end YM.Integration.WilsonConditionalTaylorWheelBookedCoil
end
