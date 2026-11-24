import YM.Integration.WilsonPositionProgramTrialPublicJointFirstSource

/-! Gather the complete fitted basis, including test derivatives, separately at each true K site. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFirstFibre
open RG Lattice Wilson Tree Source Labels XSpace XSpace.Cirrus PowerSeries Finset Precision
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard PhysicalNext.Repeat.Legato WilsonIndependentRawRosterWord
open WilsonIndependentSpoutRosterCashier (complex)
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedNamedPair (printed)
open WilsonOriginalPublicNodalBufferedCellRow (Stamps Source gain bank profile)
open WilsonOriginalPublicNodalBufferedCellFilm (Sites Seats Disp full entry paper)
open WilsonPositionProgramTrialPublicCellHull (hull)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
  (Y:Sample 2)(T:(i:Fin (n+1))→Rarity (D i))(x:Fin (n+1)→ℝ)(y σ:ℝ)(sp:0<σ)(o:Fin (n+1)→CellR)
local notation "F_" i:max => R.family.labels.level (d i)

def fee (ξ:Disp n)(i:Fin (n+1))(z:Lattice.Cover)(a:Alma (F_ i)):ℝ:=
  drumB (d i) (x i)*jewelBloom (cut i) a (wheelC (x i) y z (profile D T x y σ sp o ξ i).ψ (o i))

def money (c:Source R d)(ξ:Disp n)(i:Fin (n+1))(z:Lattice.Cover)(a:Alma (F_ i)):ℂ⟦X⟧:=
  PowerSeries.C (fee R d D cut T x y σ sp o ξ i z a:ℂ)*complex (c i a)

def field (c:Source R d)(ξ:Disp n)(i:Fin (n+1))(z:Lattice.Cover):Bare.Series (W.tree Y.F.p) G:=
  ∑a:Alma (F_ i),Bare.scalar (W.tree Y.F.p) (money R d D cut T x y σ sp o c ξ i z a) *
    printed R W Y (kind i) (d i) z (sheet (F_ i) a)

theorem price (c:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover)(a:Stamps R d):
  (∏i,money R d D cut T x y σ sp o c ξ i (z i) (a i))=
    PowerSeries.C (gain R d D cut T x y σ sp o ξ z a:ℂ)*complex (∏i,c i (a i)):=by
  have castFee:(gain R d D cut T x y σ sp o ξ z a:ℂ)=∏i,(fee R d D cut T x y σ sp o ξ i (z i) (a i):ℂ):=
    map_prod Complex.ofRealHom _ _
  simp only [money,prod_mul_distrib,castFee,map_prod]

theorem original (c:Source R d)(ξ:Disp n)(z:Fin (n+1)→Lattice.Cover):
    Bare.normalized (W.tree Y.F.p) G (∏i,field R W kind d D cut Y T x y σ sp o c ξ i (z i))=
      ∑a:Stamps R d,PowerSeries.C (gain R d D cut T x y σ sp o ξ z a:ℂ)*bank R W kind d Y c z a:=by
  unfold field
  rw [Fintype.prod_sum,map_sum]
  apply sum_congr rfl
  intro a _
  rw [prod_mul_distrib]
  have all:(∏i,Bare.scalar (G:=G) (W.tree Y.F.p) (money R d D cut T x y σ sp o c ξ i (z i) (a i)))=
      Bare.scalar (W.tree Y.F.p) (∏i,money R d D cut T x y σ sp o c ξ i (z i) (a i)):=by
    simp only [Bare.scalar,map_prod]
  rw [all,Bare.normalized_scalar,price]
  unfold WilsonOriginalPublicNodalBufferedCellRow.bank film
  rw [WilsonPositionProgramTrialPublicJointFirstSource.count,mul_assoc]
  rfl

def rearrange (H:Sites (n:=n)):Seats R d H ≃ ((i:Fin (n+1))→(H i))×Stamps R d where
  toFun u:=(fun i=>(u i).1,fun i=>(u i).2)
  invFun p:=fun i=>(p.1 i,p.2 i)
  left_inv _:=rfl
  right_inv _:=rfl

theorem posted (H:Sites (n:=n))(c:Source R d)(ξ:Disp n):
    full R W kind d D cut Y T x y σ sp o H c ξ=
      ∑z:((i:Fin (n+1))→(H i)),Bare.normalized (W.tree Y.F.p) G
        (∏i,field R W kind d D cut Y T x y σ sp o c ξ i (z i).val):=by
  simp_rw [original R W kind d D cut Y T x y σ sp o c ξ]
  unfold full
  let f:=fun z:((i:Fin (n+1))→(H i))×Stamps R d=>entry R W kind d D cut Y T x y σ sp o c ξ ((rearrange R d H).symm z)
  calc
    _=∑z:((i:Fin (n+1))→(H i))×Stamps R d,f z:=by
      apply Fintype.sum_equiv (rearrange R d H)
      intro u
      rfl
    _=_:=Fintype.sum_prod_type f

end YM.Integration.WilsonPositionProgramTrialPublicJointFirstFibre
end
