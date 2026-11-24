import YM.Integration.WilsonMarkedIndependentMixedMomentMeasure

/-! Hear the whole integrated center on the original joint test while
retaining the finite and covered moment on its real rooted positions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedCenterTensor
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Winding WilsonCoeffUV.Blue Source Source.Drops Labels
open WilsonMarkedIndependentMixedMomentTensor (Tensor logged)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open scoped Classical BigOperators Topology
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{D:ι→ℕ}{m e:ℕ}{n:ℕ→Side}

omit [Fintype ι] [DecidableEq ι] in
private def pageAt (i:ι):Volume (D i)→L[ℝ] Pier D:=
  let L:Volume (D i)→ₗ[ℝ]Pier D:={
    toFun v:=⟨fun t=>slice v (t i),(slice_ct _).comp (continuous_apply i)⟩
    map_add' _ _:=by ext;rfl
    map_smul' _ _:=by ext;rfl}
  L.mkContinuous 1 fun v=>by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun t=>registry v (t i).1 (t i).2

/-- The target contains the entire continuous center dependence. -/
def tests (u y:ℝ)(F:Garland D)(q:ι → Cover)(S:Finset ι):Pen D S→L[ℝ] Lounge:=
  let A:ContinuousMap CellR (WilsonCoeffUV.Wheel.Table D S):=⟨fun z=>seaMark (lyra u y z F q) S,by
    apply Continuous.subtype_mk
    have h:Continuous (fun z=>∏i∈S,pageAt (D:=D) i (wheelC u y (q i) (F i).ψ z)):=
      continuous_finsetProd S (fun i _=>(pageAt (D:=D) i).continuous.comp (wheelC u y (q i) (F i).ψ).continuous)
    exact h.congr fun z=>by ext v;simp only [ContinuousMap.prod_apply,folio,ContinuousMap.coe_mk];rfl⟩
  let L:Pen D S→ₗ[ℝ]Lounge:={
    toFun P:=⟨fun z=>P (A z),P.continuous.comp A.continuous⟩
    map_add' _ _:=by ext;rfl
    map_smul' _ _:=by ext;rfl}
  L.mkContinuous ‖A‖ fun P=>by
    rw [mul_comm]
    exact (ContinuousMap.norm_le _ (by positivity)).mpr fun z=>
      (P.le_opNorm (A z)).trans (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm A z) (norm_nonneg _))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem tests_apply (u y:ℝ)(F:Garland D)(q:ι → Cover)(S:Finset ι)(U:Pen D S)(z:CellR):
    tests u y F q S U z=touch (lyra u y z F q) S U:=rfl

def integral (u y:ℝ)(F:Garland D)(k:ι→ℕ)(Y:Outerm G D):Era G Lounge:=
  ∑q∈boxes u y F,lyric u k • tuftV (tests u y F q univ) (Y q univ)

theorem center (u y:ℝ)(F:Garland D)(k:ι→ℕ)(Y:Outerm G D)(z:CellR):
    locale z (integral u y F k Y)=Finale u y z F k Y:=by
  unfold integral Finale
  rw [shoreSum]
  apply sum_congr rfl
  intro q _
  exact congr_arg (lyric u k • ·) (show locale z (tuftV (tests u y F q univ) (Y q univ))=
    scrollR u y z F Y q from rfl)

theorem measured {u y:ℝ}{k:ι→ℕ}(F:Garland D)(Y:ℕ→Outerm G D){s B:ℝ}
    (growth:Tendsto (fun p=>(n p).val) atTop atTop)(width:0<s)(budget:1≤B)
    (paid:∀ᶠp:ℕ in atTop,∀N,m≤N → PairedAt e (Y N) (n p) s B):
    Tensor G Lounge m e n (fun p=>catchW s (n p)) (fun N=>integral u y F k (AuthSum (Y N))):=by
  apply WilsonMarkedIndependentMixedMomentTensor.sum _ _ (fun p=>catch_hot s (n p))
  intro x _
  apply WilsonMarkedIndependentMixedMomentTensor.smul
  have care:=WilsonMarkedIndependentMixedMomentProduct.moment (G:=G) (m:=m) (e:=e) (n:=n)
    (fun N=>Y N x) (fun p=>catch_hot s (n p)) univ
    (fun J _=>logged growth width budget paid x J)
  intro i hi r v
  exact WilsonMarkedIndependentMixedMomentPrice.mapped (tests u y F x univ) (care i hi r v)

theorem separate {Y Z:Era G Lounge}(h:∀z,locale z Y=locale z Z):Y=Z:=by
  apply Prod.ext
  · funext n e r x
    exact ContinuousMap.ext fun z=>congr_arg (fun R:Era G ℝ=>R.1 n e r x) (h z)
  · funext e r x
    exact ContinuousMap.ext fun z=>congr_arg (fun R:Era G ℝ=>R.2 e r x) (h z)

end YM.Integration.WilsonMarkedIndependentMixedCenterTensor
end
