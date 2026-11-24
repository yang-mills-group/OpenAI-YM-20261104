import YM.Integration.WilsonOriginalPublicRelativeGramNativeSites

/-! Equality of the actual unconditioned Wilson cylinder on the common
translated K sites and on the original f-grid. Each label remains unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeLaw
open Filter Set Function Lattice Wilson RG Source OPE PhysicalNext.Repeat.Legato Extraction XSpace XSpace.Cirrus
open WilsonOriginalPublicRelativeGramAddresses (ports)
open WilsonOriginalPublicRelativeGramNativeSites (shift sample layout)
open scoped Classical Topology BigOperators

variable {G:Gauge}(R:Run G){n:ℕ}(W:Finset E4)(x:Points n)

theorem dates (M:Mesh){f K N:ℕ}(live:f≤K)(before:K≤N)(p:ℕ)(s r:ℝ)(i:Fin n):
    Cells.location R.family.S K N p ((sample R W x M live s r).layout i)=
      Cells.location R.family.S f N p (ports R W x f r i)+Cells.location R.family.S f N p (shift M (R.family.S.a f/s)):=by
  change Cells.location R.family.S K N p (OPE.zoom R.family.S live _)=_
  rw [OPE.zoom_local (C:=R.family) _ live N p before,Extraction.Order.location_add]

theorem original (M:Mesh){f K N:ℕ}(live:f≤K)(before:K≤N)(p:ℕ)(s r:ℝ)
    (d:Caps n)(v:R.family.book.Vector d)(ready:∀i,R.family.ref (d i)≤N):
    R.family.ensemble d (fun i=>Cells.location R.family.S K N p ((sample R W x M live s r).layout i)) v=
      R.family.ensemble d (fun i=>Cells.location R.family.S f N p (ports R W x f r i)) v:=by
  let labels:Fin n→ R.family.book.Token:=fun i=>⟨d i,v i⟩
  let loc:=fun i=>Cells.location R.family.S f N p (ports R W x f r i)
  have atSite:=funext (dates R W x M live before p s r)
  rw [atSite]
  exact R.family.anchored R.makes labels ready _ loc

theorem reference {f:Extraction.Order}(ℓ:Ultrafilter (ℕ×ℕ))(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (K:ℕ):∀ᶠz:ℕ×ℕ in (ℓ:Filter (ℕ×ℕ)),K≤z.1:=by
  apply Filter.Eventually.filter_mono below
  rw [Extraction.Order.fused]
  exact Eventually.of_forall fun _=>f.mesh.monotone.tendsto_atTop.eventually_ge_atTop K

end YM.Integration.WilsonOriginalPublicRelativeGramNativeLaw
