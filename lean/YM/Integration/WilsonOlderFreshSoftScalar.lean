import YM.Integration.WilsonOlderFreshSoftStops

/-! The deposited scalar on every actual folded period carries its previous thermal series. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftScalar
open Function Filter Finset Matrix Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open WilsonOlderFreshSoftStops (scalarOnly)
open scoped Classical BigOperators Topology
variable {G:Gauge}

private theorem extract {U:Type*}(X:Pal ℝ U):X-lop X=uband (ScalarTrim X):=by
  have h:=lop_pres X
  exact sub_eq_iff_eq_add.mpr (h.trans (add_comm ..))

theorem finite (P:Era G ℝ)(n:Side):(scalarOnly P).1 n=uband (ScalarTrim (P.1 n)):=
  extract (P.1 n)

theorem cover (P:Era G ℝ):(scalarOnly P).2=uband (ScalarTrim P.2):=extract P.2

def recoiled (A:Levels G)(O:ChartRatio G)(N w v:ℕ)(C:Side → Cost)(n:Side):Cost:=
  if _:v<w then reel (ratioHigh A O N v) (recoiled A O N w (v+1) C (n*(ll A v).L))
  else C n
termination_by w-v

private theorem step (A:Levels G)(O:ChartRatio G)(N i h:ℕ)(X:Era G ℝ)(C:Side → Cost)
    (income:∀n,X.1 n=uband (C n))(n:Side):
    (verseI A O i N h X).1 n = uband (reel (ratioHigh A O N i) (C (n*(ll A i).L))):=by
  change Blue.mix _ (reed _ _ _ _ _ _ _ (X.1 _))=_
  rw [income,rumble,reset_zinc]

theorem received (A:Levels G)(O:ChartRatio G)(N k w v:ℕ)(vw:v≤w)(P:Era G ℝ)(n:Side):
    (cruises A O N k w v (scalarOnly P)).1 n=
      uband (recoiled A O N w v (fun t=>ScalarTrim (P.1 t)) n):=by
  induction vw using Nat.decreasingInduction generalizing n with
  | self =>
    rw [cruises_top,recoiled,dif_neg (lt_irrefl w)]
    exact finite P n
  | of_succ i hi ih =>
    rw [cruises_sub _ _ _ _ _ hi,recoiled,dif_pos hi]
    exact step A O N i k _ _ ih n

theorem constant (A:Levels G)(O:ChartRatio G)(N w v:ℕ)(vw:v≤w)(r:ℝ)(n:Side):
    recoiled A O N w v (fun _=>PowerSeries.C (R:=ℝ) r) n=PowerSeries.C (R:=ℝ) r:=by
  induction vw using Nat.decreasingInduction generalizing n with
  | self=>rw [recoiled,dif_neg (lt_irrefl w)]
  | of_succ i hi ih=>
    rw [recoiled,dif_pos hi,ih]
    change (substAlgHom _ (PowerSeries.C (R:=ℝ) r))=_
    exact (substAlgHom _).commutes r

end YM.Integration.WilsonOlderFreshSoftScalar
end
