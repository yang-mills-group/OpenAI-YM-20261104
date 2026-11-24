import YM.Integration.WilsonMacroscopicRichFlatTranslation
import YM.RG05Readout.Harvest.Prices

/-! Each rotated child in the original degree-zero reporting census can
be placed on its true ultraviolet stencil before conditioning at the older
gauge. The common fine shift is the actual lattice embedding of that child. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source OPE.Therm Push.GridApprox
open RG05Readout Address Harvest Records Many Native MergeProof Accent PhysicalNext.Repeat.Legato Extra.Histories
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (N p:ℕ)

private theorem pushed (A:History G) (j:ℕ) (f:Config G (A.S.side j p)→ℂ) {k:ℕ} (hk:k≤j):
    gust A N p j f k hk=pushTo A N p hk f:=by
  induction hk using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ i hi ih=>rw [gust_step A N p j f hi,Birth.push_first A N p hi,ih]

/-- Exact equality of the two original unnormalised densities at every
coarse gauge, including all rough fields. -/
theorem covariance {k:ℕ} (top:k≤N) (q:Site (R.family.side k p)) (X:Goods G (R.family.side N p)) (smooth:Continuous X):
    dyes R.family k N p top (X ∘ Lattice.pull 1 (anchor R.family.S p top q))=
      (dyes R.family k N p top X) ∘ Lattice.pull 1 q:=by
  let w (U:Config G (R.family.side N p)):ℂ:=((R.family.path.rep N p N).eval U:ℂ)*X U
  let b:=anchor R.family.S p top q
  have budget:Integrable w (prior G _):=dye_grow R.makes smooth
  have shift:(fun U=>((R.family.path.rep N p N).eval U:ℂ)*(X ∘ Lattice.pull 1 b) U)=w ∘ Lattice.pull 1 b:=by
    funext U;dsimp only [Function.comp_apply,w]
    rw [WardBin.Wheels.rep_spins (H:=R.family.path) 1 R.makes.wilson (le_refl N) U b]
  unfold dyes;rw [pushed,pushed]
  change pushTo R.family.path N p top (fun U=>((R.family.path.rep N p N).eval U:ℂ)*(X ∘ Lattice.pull 1 b) U)=_
  rw [shift];exact WilsonMacroscopicRichFlatTranslation.pushed R.family.path N p top q w budget

/-- All original marked sites will undergo one common translation. The body
also undergoes its authentic affine pullback in the same child. -/
def arrangement {n:ℕ} (top:n+1≤N) (F:Bin G (R.family.side N p)) (g:Body) (i:Bud R.family p n):Goods G (R.family.side N p):=
  F (headFee R.family p n i g) ∘ Lattice.pull 1 (anchor R.family.S p top (child R.family p n i))

theorem original {n:ℕ} (top:n+1≤N) (F:Bin G (R.family.side N p)) (timed:timely F) (g:Body) (V:Config G (R.family.side n p)):
    pulls R.family p N n 0 top F n le_rfl g V/liftVac R.family.path N p n V=
      (Fintype.card (Bud R.family p n):ℂ)⁻¹*∑i:Bud R.family p n,
        dyes R.family n N p (n.le_succ.trans top) (arrangement R N p top F g i) V/liftVac R.family.path N p n V:=by
  let S:=R.family.path.levels.clock.op n p
  let β:=R.family.path.β N p (n+1)
  have row (i:Bud R.family p n):S.push β (sailS R.family n p (arises R.family p N n top F) g i)=
      dyes R.family n N p (n.le_succ.trans top) (arrangement R N p top F g i):=by
    let X:=F (headFee R.family p n i g)
    change S.push β ((dyes R.family (n+1) N p top X) ∘ Lattice.pull 1 (child R.family p n i))=_
    rw [←covariance R N p top (child R.family p n i) X (timed _)]
    change S.push β (gust R.family.path N p N _ (n+1) top)=gust R.family.path N p N _ n (n.le_succ.trans top)
    exact (gust_step R.family.path N p N _ top).symm
  rw [wakes top F];unfold journey Address.average blast
  simp only [pow_zero,one_smul,Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  change ((Fintype.card (Bud R.family p n):ℂ)⁻¹*(∑i:Bud R.family p n,S.push β (sailS R.family n p (arises R.family p N n top F) g i) V))/_=_
  simp_rw [row];rw [mul_div_assoc,Finset.sum_div]

end YM.Integration.WilsonPositionSeparatedProfileCenteredBranch
