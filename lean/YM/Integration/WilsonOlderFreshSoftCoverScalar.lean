import YM.Integration.WilsonOlderFreshSoftScalar

/-! All previous zero-rank deposits follow the independently appointed kinetic clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftCoverScalar
open Function Filter Finset Matrix Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open WilsonOlderFreshSoftStops (scalarOnly)
open scoped Classical BigOperators Topology
variable {G:Gauge}

def uniform (G:Gauge)(C:Cost):Era G ℝ:=(fun _=>uband C,uband C)

private theorem licensed (C:Cost)(k:ℕ):Auth k (uniform G C):=by
  refine ⟨fun i t=>?_,fun _=>uband_length _ _ k,fun _=>uband_cost _ _,fun n=>?_⟩
  · cases t with
    | succ t=>unfold uniform;simp_rw [uband,shine_dark (by omega:0≠t+1)];exact Bends.zero
    | zero=>
      refine ⟨fun _=>tendsto_const_nhds,1,‖(uniform G C).2 i 0 Fin.elim0‖,one_pos,
        .of_forall fun n=>⟨norm_nonneg _,fun x=>?_⟩⟩
      simp only [uniform,uband,shine_lit];simp [tread,league,tor]
  apply certify (k:=0) (ι:=Unit) (fun _=>LinearMap.id) (fun _ _ z=>z ()) _ (uband_length (Woods G n) C 0)
  intro x
  rw [show ply LinearMap.id (uband (U:=Woods G n) C)=uband C from rfl,uband_flash]
  intro Z I a X X' h
  rw [income,income]

private theorem move (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N i k:ℕ)(live:i<N)(C:Cost):
    (verseI A O i N k (uniform G C)).2=uband (reel (ratioHigh A O N i) C):=by
  let H:=verseI A O i N k (uniform G C)
  have lic:Auth k H:=(licensed (G:=G) C k).verse A live simple localO
  have paid (n:Side):H.1 n=uband (reel (ratioHigh A O N i) C):=by
    change Blue.mix _ (reed _ _ _ _ _ _ _ (uband C))=_
    rw [rumble,reset_zinc]
  funext e r x
  apply tendsto_nhds_unique ((lic.wing e r).point x)
  refine tendsto_const_nhds.congr' (.of_forall fun n=>?_)
  change _=H.1 n e r (slideC n x)
  rw [paid]
  cases r with
  | zero=>simp only [uband,shine_lit]
  | succ r=>simp only [uband,shine_dark (by omega:0≠r+1),Pi.zero_apply]

def clock (A:Levels G)(O:ChartRatio G)(N w v:ℕ)(C:Cost):Cost:=
  if _:v<w then reel (ratioHigh A O N v) (clock A O N w (v+1) C) else C
termination_by w-v

theorem received (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N k w v:ℕ)(wn:w≤N)(vw:v≤w)(P:Era G ℝ):
    (cruises A O N k w v (scalarOnly P)).2=uband (clock A O N w v (ScalarTrim P.2)):=by
  induction vw using Nat.decreasingInduction with
  | self=>
    rw [cruises_top,clock,dif_neg (lt_irrefl w)]
    exact WilsonOlderFreshSoftScalar.cover P
  | of_succ i hi ih=>
    rw [cruises_sub _ _ _ _ _ hi,clock,dif_pos hi]
    let C:=clock A O N w (i+1) (ScalarTrim P.2)
    have exactMove:=move A O simple localO N i k (hi.trans_le wn) C
    unfold verseI at exactMove ⊢
    dsimp only [Prod.snd,uniform] at exactMove ⊢
    rw [ih]
    exact exactMove

theorem constant (A:Levels G)(O:ChartRatio G)(N w v:ℕ)(vw:v≤w)(r:ℝ):
    clock A O N w v (PowerSeries.C (R:=ℝ) r)=PowerSeries.C (R:=ℝ) r:=by
  induction vw using Nat.decreasingInduction with
  | self=>rw [clock,dif_neg (lt_irrefl w)]
  | of_succ i hi ih=>rw [clock,dif_pos hi,ih];exact (substAlgHom _).commutes r

end YM.Integration.WilsonOlderFreshSoftCoverScalar
end
