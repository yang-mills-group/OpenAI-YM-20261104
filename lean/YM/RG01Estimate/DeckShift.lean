import YM.RG01Estimate.ExtraDeck
/-!
 # Exact kernel comparison for ANY invoice of short terms that also
 uses the extra action vertices. This generalizes blanket equation of
 Purloin to persistent supported log extras. No replacing random charges
 outside the compact hull; locality of projected laws on selected b itself
 proved via Purloin's canonical marginal on PODIUM plus exact vertex transforms
 under warrant. Use with DeckSpark proof.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Greenbelt Deck.Stellar Poll Pond MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
variable {Γ : Type}
variable {a v W K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta)
    {V:Lex Γ f}{V':Lex Γ F}(A:Charts (h:=h) (H:=H) hC he R R' V V') {U: Finset (Header Γ C F)} {m : ℕ}
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (warps (Γ:=Γ) (Lace.project (h:=h) (H:=H) hC he)) U)
    (hS:C'.unionP (songs («S»:=stepped Q H) V' U)⊆neighbors n Z)
    (hw:∀ i∈ U,fit R'.path i ≤ radiusB p)
    (hU: ∀ i, regularFoot (decreed H) 0 (radiusB p) R' (V' i)⊆neighbors m ((decreed H).parent i.1))
    (hC': 2*(m+3)<c.val)
section shelter
variable {E: Forest (stepped Q h).ratio}{E':Forest (stepped Q H).ratio} {X: Coat T E} {X': Coat T' E'}
    (R₀ : Stellar hC he K p X X') (hf : X'.manifest) (hm:X.manifest) (hK:X.width=o.K) (k k':Finset ℕ)
include H hC he A C' c' ht hx hb hf hm hK hZ hd hS hw hU hC' R₀
lemma correspondence : X'.attains R' J.table W o.a k J.halo (songs («S»:=stepped Q H) V' U)=X.attains R J.table W o.a k' J.halo
       (songs («S»:=stepped Q h) V (U.image (warps (L)))) := by
  let q:=songs («S»:=stepped Q H) V' U; let u:=songs («S»:=stepped Q h) V (U.image (warps (L)))
  let I:= podium (Y) G (C'.unionP q) X'.B; let g:= X'.body R' J.table W o.a k J.halo q; let f:= X.body R J.table W o.a k' J.halo u
  let l:=L; let x' := radiusB p
  have hz : X'.width=o.K:= R₀.wit.symm.trans hK
  have hi i (hi:i∈I):separation Z (along (Y) i) ≤ n:= (neighbors_mem ..).1 (hS <| (mem_filter.mp hi).2 (along (Y) i) (by rw [separation_self]; omega))
  have hj:= Stellar.tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he -- namespace check
  let y:= seed (G:=G) l; let e:↥I ↪ Tubular _ G:= ⟨fun i=> y i.val, fun i k h=> Subtype.ext (hj.point (k:=n) (by omega) Z _ _ (hi _ i.2) (hi _ k.2) h)⟩
  have hE : circuit I X'.relating=X.relating.submatrix e e:= by ext i j; apply R₀.allocates hZ; refine (separation_triangle _ Z _).trans ?_; rw [separation_comm _ Z]; have hz:=hi _ i.2; have hk:=hi _ j.2; dsimp only; omega
  let a:= arch I X'.relating; have hI:MeasurePreserving (swim I) X'.dice a:= orbit (C'.laws.data.localP E' X' R₀.reached hz hf).sails.fullC.posSemidef I; have hl:MeasurePreserving (Stellar.mount e) X.dice a:= by unfold a arch; rw [hE]; exact Stellar.loss e _ (c'.laws.data.localP E X R₀.equal hK hm).sails.fullC.posSemidef
  have hx (Y₁:E.Slice G) (Y₂:E'.Slice G): (∫ z,g (Y₂,z) ∂X'.dice) = ∫ z,f (Y₁,z) ∂X.dice:= by
    let a z:=g (Y₂,spill I z); let b z:=g (Y₂,z)
    have ha : Measurable b:= ((X'.body_b J.table_exists (R₀.reached.symm ▸ C'.laws.intake) (by rw [R₀.reached,hz]; exact C'.laws.data.access) ..)).comp (measurable_const.prodMk measurable_id)
    have hp : Measurable a:= ha.comp (spill_m I)
    have he (u v) (h : swim I u=swim I v): b u=b v:= C'.concord q (X'.wrapY Y₂) (X'.wrapY Y₂) ⟨Village.refl _ _,(observe _).1 h,fun _ _=> Iff.rfl⟩ R₀.reached (Finset.Subset.refl _)
    have hy z:f (Y₁,z)=a (Stellar.mount e z):= by
      rw [show a (Stellar.mount e z)=b (blow l z) from he _ _ (Pond.settled _ _)]; change _=(X'.wrapY Y₂).term _ _ _ _ _ _ _ _
      unfold f Coat.body; dsimp only; unfold q u Coat.term songs; rw [prod_map,prod_map, prod_image hd]
      exact Finset.prod_congr rfl (fun i hi=> (loops_with A ht hx (R₀.draws Y₁ Y₂) hb J.table i (hw i hi) W o.a z _ hU hC' ..).symm) -- order
    rw [Pond.gathered (spill I) (spill_m I) hI (Pond.settled I) he ha]; change (∫ z,a z ∂_) =_
    rw [← hl.map_eq,MeasureTheory.integral_map (by exact hl.measurable.aemeasurable) hp.aestronglyMeasurable]; exact integral_congr_ae (Eventually.of_forall fun i=> (hy i).symm)
  unfold attains; rw [integral_prod _ (C'.integrated X' R₀.reached hz hf k _),integral_prod _ (c'.integrated X R₀.equal hK hm k' _)]
  let D := (∫ y,g (X'.Y,y) ∂X'.dice)
  have ht (z:E'.Slice G): (∫ y,g (z,y) ∂X'.dice)= D:= (hx X.Y z).trans (hx X.Y X'.Y).symm
  have hk (z:E.Slice G): (∫ y,f (z,y) ∂X.dice)=D:= (hx z _).symm
  change (∫ z:E'.Slice G, (∫ y,g (z,y) ∂X'.dice) ∂E'.order G)=(∫ z:E.Slice G, (∫ y,f (z,y) ∂X.dice) ∂E.order G)
  simp_rw [ht,hk]; simp
end shelter
end YM.RG01Estimate.Evoc
