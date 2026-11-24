import YM.Integration.WilsonOriginalTwoFlatIRFlatEarned
import YM.Integration.WilsonOlderFreshSoftSocketTotal
import YM.Integration.WilsonReceivedChronologicalSocket

/-! The commissioned original scalar and its fixed-child thermal reading share every term. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 640000
noncomputable section
namespace YM.Integration.WilsonMovingForkSocketScalar
open Finset Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Winding WilsonFiniteMarkedHistoryStep
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonIndependentCollarDatedPrior (onLevels)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedChronologicalSocket (extend)
open WilsonOriginalTwoFlatIRFlatEarned (whole)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonOlderFreshHybridClock (flat)
open WilsonThermometerDeclaredSeeds (Choice)
open ActualRunPhysicalPages Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped BigOperators Classical
variable {G:Gauge}{n e:ℕ}{R:Run G}{D d:Fin n→ℕ}{N per K c j:ℕ}
    {V:Realm G (e+1) Credit.leanC}{draw:V.draws=R.family.path.levels}
    (κ:(i:Fin n)→Knob (D i))(pt:Fin n→Chamber)(cells:Digits V.draws (Fin n))
    (y:Fin n → Cover)(t:Case D)
local notation "L₀" => R.family.path.levels
local notation "digits₀" => onLevels draw cells
local notation "location" => address L₀ digits₀ (c-(j+1)) (j+1) y

theorem original (q:(i:Fin n)→Choice R d i)(x:Fin n→ℂ)(g:ℝ)(p:ℕ)(S:Finset (Fin n)):
    whole (R:=R) (N:=N) (K:=K) (c:=c) (j:=j) (draw:=draw) κ pt cells q y t x g p S=
    (∏i∈S,x i)*(flat (WilsonOlderFreshSoftSocketRestored.stopped R d N K c (j+1) digits₀
      location S (touch t S) (start R d κ pt q)) p g:ℂ):=by
  let E:=WilsonOlderFreshSoftSocketRestored.stopped R d N K c (j+1) digits₀
    location S (touch t S) (start R d κ pt q)
  change (∑i∈range (p+1),(g:ℂ)^i*((∏u∈S,x u)*((E.2 i 0 Fin.elim0:ℝ):ℂ)))=
    (∏u∈S,x u)*((∑i∈range (p+1),g^i*(E.2 i 0 Fin.elim0):ℝ):ℂ)
  rw [Complex.ofReal_sum,mul_sum]
  apply sum_congr rfl
  intro i _
  rw [Complex.ofReal_mul,Complex.ofReal_pow]
  ring

theorem filed (w:(i:Fin n)→R.family.label (d i))(g:ℝ)(p:ℕ)(S:Finset (Fin n)):
    (∑q:Selection R d S,weight R d N per K w S q*
      whole (R:=R) (N:=N) (K:=K) (c:=c) (j:=j) (draw:=draw) κ pt cells (extend R d S q)
        y t (fun _=>1) g p S)=
    normalized R d κ pt N per K c (j+1) digits₀ S w location (touch t S) p g:=by
  unfold normalized
  apply sum_congr rfl
  intro q _
  rw [original κ pt cells y t]
  simp only [prod_const_one,one_mul]
  rfl

end YM.Integration.WilsonMovingForkSocketScalar
end
