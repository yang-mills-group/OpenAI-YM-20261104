import YM.Integration.WilsonOlderFreshSoftSocketFaces

/-! Restrict a marked history at its initial printed stencils. An occupied
singleton has exactly the same finite response and source wage on either
roster, with the actual angular test evaluated at its own site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseSingleSlot
open Function Finset Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open OriginalMarkedSourceComet
open scoped Classical BigOperators


open WilsonCoeffUV.Mer WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Wheel.Motion
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding
open IndependentSourcePathFamily

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}
  {B:I→Type}[∀i,Fintype (B i)](X:(i:I)→B i→Seed G (D i))
  (t:Finset I)(A:Case D)(z:I→ Cover)(j:t)(n:Side)

private def token {d:ℕ}(u:Seed G d):=colour u.path u.color u.weight u.quadrant

omit [Fintype I] in
theorem landed (T:TowerS G (D j.val))(w:Cover):
    readO A (cn D j.val T w) n=
      readO (fun a:t=>A a.val) (cn (fun a:t=>D a.val) j T w) n:=by
  unfold readO cn pPly
  simp only [shifted,tuftV,ply_skew]
  apply congrArg flash
  apply congrArg (skewV (wrap n w))
  funext e r v
  change touch A {j.val} (petal D j.val (T.1 n e r v))=
    touch (fun a:t=>A a.val) {j} (petal (fun a:t=>D a.val) j (T.1 n e r v))
  rw [petal_hit,petal_hit]

omit [Fintype I] [(i:I)→Fintype (B i)] in
private theorem fee {i:I}(m:B i)(paid:(X i m).rank≤k i+(X i m).head):
    Auth (k i) (source D i (token (X i m)) (X i m).knob (X i m).point (X i m).head (z i)):=
  certified D i _ (invariant _ _ _ _) _ _ _ _ paid _

theorem original (paid:∀i b,(X i b).rank≤k i+(X i b).head):
    readO A (independent X z {j.val}) n=
      readO (fun a:t=>A a.val) (independent (fun a:t=>X a.val) (fun a:t=>z a.val) {j}) n:=by
  classical
  rw [IndependentSourcePathFamily.singleton,IndependentSourcePathFamily.singleton]
  let lo (m:B j.val):=source D j.val (token (X j.val m)) (X j.val m).knob (X j.val m).point (X j.val m).head (z j.val)
  let hi (m:B j.val):=source (fun a:t=>D a.val) j (token (X j.val m)) (X j.val m).knob (X j.val m).point (X j.val m).head (z j.val)
  change readO A (∑m,lo m) n=readO (fun a:t=>A a.val) (∑m,hi m) n
  have low (m:B j.val) (_:m∈(univ:Finset (B j.val))):Auth (k j.val) (lo m):=fee X z m (paid j.val m)
  have high (m:B j.val) (_:m∈(univ:Finset (B j.val))):Auth (k j.val) (hi m):=
    fee (fun a:t=>X a.val) (fun a:t=>z a.val) m (k:=fun a:t=>k a.val) (paid j.val m)
  rw [read_Sum A n low,read_Sum (fun a:t=>A a.val) n high]
  apply Finset.sum_congr rfl
  intro m _
  exact landed t A j n (volumeR (current (token (X j.val m))
    (claim (D j.val) (X j.val m).knob (X j.val m).point)) (X j.val m).head) (z j.val)

end YM.Integration.WilsonOriginalTwoFlatRoseSingleSlot
