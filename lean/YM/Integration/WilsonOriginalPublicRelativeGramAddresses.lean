import YM.Integration.WilsonOriginalPublicRelativeGramFreePanel
import YM.OPE.Eye.Cloud

/-! Signed reference nodes on one true grid, approaching the elected free
placements after dilation. The two marked sites use distinct native residues
in each coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramAddresses
open Filter Finset Function Set WithLp Lattice Wilson RG Source OPE
open PhysicalNext.Repeat.Legato Extraction
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(W:Finset E4)(x:Points n)
def ports (b:ℕ)(r:ℝ):Fin n→ Cover:=
  Cloud.grid W (R.family.S.a b / r) x.ofLp (fun _ _=>0)
def shape (δ:ℝ):Points n:=points (Cloud.placeGrid W δ x.ofLp (fun _ _=>0))

theorem placed (b:ℕ){r:ℝ}(rp:0<r):
    Extraction.Order.grid R.family b (ports R W x b r)=r • shape W x (R.family.S.a b/r):=by
  ext i a
  change _*(Cloud.grid W (R.family.S.a b/r) x.ofLp (fun _ _=>0) i a:ℝ)=
    r*((R.family.S.a b/r)*(Cloud.grid W (R.family.S.a b/r) x.ofLp (fun _ _=>0) i a:ℝ))
  rw [←mul_assoc,mul_div_cancel₀ _ rp.ne']

theorem screened (b:ℕ){r:ℝ}(rp:0<r):
    Extraction.Order.grid R.family b (ports R W x b r)∈generic n:=by
  rw [placed R W x b rp]
  have ok:=Cloud.screened W (R.family.S.a b/r) (div_pos (R.family.S.a_pos b) rp) x.ofLp (fun _ _=>0)
  intro a i j same
  apply ok a
  change r*_ = r*_ at same
  exact (mul_left_cancel₀ rp.ne' same)

theorem residues (b:ℕ)(r:ℝ)(i:Fin n)(a:Axis):
    (ports R W x b r i a)%Cloud.count (Fin n) W = Cloud.residue W (R.family.S.a b/r) i a:=
  Cloud.node_mod ..

theorem limit {Z:Type}{l:Filter Z}{δ:Z→ℝ}(dp:∀ᶠz in l,0<δ z)(fine:Tendsto δ l (𝓝 0)):
    Tendsto (fun z=>shape W x (δ z)) l (𝓝 x):=by
  let outer: Points n ≃L[ℝ] (Fin n→E4):=PiLp.continuousLinearEquiv 2 ℝ _
  apply Tendsto.comp (f:=fun z=>outer (shape W x (δ z))) (g:=outer.symm) (outer.symm.continuous.tendsto (outer x))
  apply tendsto_pi_nhds.mpr
  intro i
  let inner:E4 ≃L[ℝ] (Axis→ℝ):=PiLp.continuousLinearEquiv 2 ℝ _
  apply Tendsto.comp (f:=fun z=>inner (shape W x (δ z) i)) (g:=inner.symm) (inner.symm.continuous.tendsto (inner (x i)))
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have tariff:Tendsto (fun z=>δ z*(Cloud.count (Fin n) W:ℝ)) l (𝓝 0):=by
    simpa only [zero_mul] using fine.mul_const (Cloud.count (Fin n) W:ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) _ tariff
  filter_upwards [dp] with z positive
  exact Cloud.close_zero W (δ z) positive x.ofLp i a

end YM.Integration.WilsonOriginalPublicRelativeGramAddresses
