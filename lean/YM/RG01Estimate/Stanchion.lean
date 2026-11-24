import YM.RG01Estimate.GreenEye
/-!
 # Joint cuts through any aperture enumerations. All axes in unmasked Vacuum
 bin; pay before dropping masks with their stencil. Constant rank count across periods
 in the **budgets**, not in cutoff-index: existential cut in each Rack may depend on
 period (all chosen on the same universe prior to labels/canonical reclosure).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Caddy
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height Beam Brim Match Song
open Next.Scheduling AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Meadow Marlin Trio
open Geo Footprint Animals Abacus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}(P:BudgetPoint){t w v : ℝ}{A:Listing G c}

lemma limits (q: ℕ→ℕ→Prop) (F:ℕ→ Config G c→ℝ)(H: Meadow.Budget P A.reg F t)
    (he:∀ i, F i≠0→∀ᶠ z in atTop,¬q z i) (ht:0<w) : ∀ᶠ z in atTop, Meadow.Budget P A.reg (fun i=>if q z i then F i else 0) w:= by
    let u k i := q k i ∧ F i≠0; let V:Collection.Source G c:= ⟨F,0⟩
    obtain ⟨a,h',hp⟩:=H; have hh:= Meadow.limits (P:=A) P u (h:=fun _=> V) 0 ⟨a,(Boulevard.planetary h' (fun i=> (hp i).2.1)).2.1,fun i=> (hp i).2⟩
       (fun i=> by
         by_cases h:F i=0; · exact Eventually.of_forall (fun _ hx=> hx.2 h)
         exact (he i h).mono fun _ h v=> h v.1) ht
    filter_upwards [hh] with z hz
    obtain ⟨b,hb,hB⟩:=hz; have hy i:(if q z i then F i else 0)=if u z i then F i else 0:= by unfold u; split_ifs <;> simp_all
    refine ⟨b,hB,fun i=>?_⟩
    dsimp only; rw [hy]; refine ⟨?_, by convert! hb i using 1; by_cases hh:u z i<;>simp [hh,V]⟩; split; exact (hp _).1; exact CouplingShape.reg_const _

section cut
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {A : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G A} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ s a α : ℝ} {i j k m n : ℕ} (χ : Chi)
    (H : Cash W s μ L Q o α T R) (p:Match.Alliance H H 1 0)
    (γ : ℝ) (E:Set ℕ)(r:ℕ)
local notation "p₀" => Beam.marquee H P
local notation "f₀" => Song.plusone H p χ γ

def cut (π:Finset (Magazine H)) := Song.choir (fun i=> if i∈π then Pruned.regLow H χ p E r γ i else 0) ∘ Song.pennant H

def entries (π:Finset (Magazine H)) : Finset ℕ:= (univ ×ˢ π).map (Song.pennant H).symm.toEmbedding
local notation "A₀" => Pruned.low H χ p E r γ
local notation "H₀" => Pruned.high H χ p E r γ
lemma equals_in (π:Finset (Magazine H)) (i:ℕ) : cut χ H p γ E r π i=if i∈ entries H π then (A₀).logRead i else 0 := by
   let f:=pennant H i; have he : i∈entries H π ↔ f.2∈π:= by unfold f entries; simp only [mem_map_equiv,mem_product,mem_univ,Equiv.symm_symm, true_and]
   unfold cut; simp_rw [he]; change Rim c • ((if f.2∈π then Pruned.regLow H χ p E r γ f.2 else (0:Config G c→ℝ)) ∘ f.1.view)=_
   split
   · rfl
   simp
set_option maxHeartbeats 450000 in
lemma invoice (π : ℕ → Finset (Magazine H)) (he:∀ i, Pruned.chosen H p E r i → ∀ᶠ z in atTop,i∈π z) {b b' u u' : ℝ}
    (hq: Collection.Local (p₀) P (A₀) b u)(hp:Collection.Local (p₀) P (H₀) b' u')(hw:0<w):
     ∀ᶠ z in atTop,
       let g:=cut χ H p γ E r (π z)
       Meadow.Budget P (p₀).reg g b ∧ Meadow.Budget P (p₀).reg ((f₀).logRead-g) (b'+w) ∧
         ∀ s t,Nonempty (((p₀).read (revise f₀ ((f₀).logRead-g))).Moves s t):= by
   let g z := cut χ H p γ E r (π z); let P' i:=Pruned.chosen H p E r i; let S z i:= i∈ entries H (π z)
   have hh i (hi:(A₀).logRead i ≠0): P' (pennant H i).2:= by
        contrapose! hi; unfold Pruned.low; change Rim c • (Pruned.regLow H χ p E r γ (pennant H i).2 ∘ _)= _; rw [Pruned.regLow, if_neg hi]; simp
   have hf:=Caddy.limits P (fun z i=> ¬S z i) _ (charted P hq) (fun i hi=> (he _ (hh i hi)).mono fun z hi hr=>
           hr (by unfold S entries; simp only [mem_map_equiv, Equiv.symm_symm, mem_product]; exact ⟨mem_univ _, hi⟩)) hw
   filter_upwards [hf] with z hz; intro F
   refine ⟨?_,?_,fun s t=>?_⟩
   · change Meadow.Budget _ _ (cut χ H p γ E r (π z)) _
     rw [funext (equals_in χ H p γ E r (π z))]
     convert Acquire.budget_cut (fun i=> i∈entries H (π z)) (charted _ hq) using 1
     funext i; by_cases ht:i∈entries H (π z)<;>simp [ht]
   · let f := (fun i=> @ite _ (¬S z i) (Classical.propDecidable _) ((A₀).logRead i) 0)
     have he:(f₀).logRead-F=(H₀).logRead+f:= by
         rw [Pruned.tracks H χ p E r γ]; funext i; unfold F; simp only [Pi.sub_apply,Pi.add_apply,equals_in]; unfold f S; by_cases he:i∈ entries H (π z); · rw [if_pos he, if_neg (show ¬(¬i∈ entries H (π z)) from not_not.mpr he)]; abel
         rw [if_neg he, if_pos he]; abel
     rw [he]; exact pay_bundle _ (charted _ hp) hz
   let v i:= (opus H p χ γ i)-(fun i=> if i∈π z then Pruned.regLow H χ p E r γ i else 0) i
   have he : (f₀).logRead-F=Song.choir v ∘ pennant H := by ext1 i; unfold F cut; funext y; change Rim c*_-Rim c*_=Rim c*(_-_); rw [mul_sub]; rfl
   rw [he]; exact Beam.moves H P χ p s t v

lemma low_inherits {K y:ℝ} (h: Collection.Local (p₀) P (f₀) K y): Collection.Local (p₀) P (A₀) K y:= by
    have ht:= Acquire.budget_cut (fun i:ℕ=> Pruned.chosen H p E r (pennant H i).2) (charted P h)
    have hp : (A₀).logRead=(fun i:ℕ=> if Pruned.chosen H p E r (pennant H i).2 then (f₀).logRead i else 0):= by
         funext i; change Rim c • (Pruned.regLow H χ p E r γ _ ∘ _) = _; unfold Pruned.regLow; split
         · rfl
         simp
    rw [← hp] at ht; obtain ⟨u,hv,hp⟩:=ht
    have hf:= h.family
    exact ⟨fun i=>(hp _).1,⟨hf.sym,hf.symtest,hf.meas,hf.meas_test,hf.reads,hf.reads_test,hf.permit⟩,fun s t=> Beam.moves H P χ p s t _,⟨u,fun i=> (hp i).2,hv⟩,h.expensive⟩

-- fill Crew by anchor assignment. Uses ANY furnished stencil. For Π comparison choose garner.
variable (q: ℕ) (π:Finset (Magazine H)) (u:∀ i:Magazine H,i∈π → ∀ x, Meadow.share H P x i≠0 → (Beam.contents H P i|>.support) ⊆ neighbors q x)
-- canonical cut

def rack : Rack (p₀) q (cut χ H p γ E r π) where
   atW:= entries H π
   seat i j:= Meadow.garnerAt H P j i
   bound i hi:=by rw [equals_in, if_neg hi]
   sums i _:= Meadow.paysOne H P i
   paid i _ x:= Meadow.nonnegative H P x i
   priced i hi x h:= by
      unfold entries at hi; simp only [mem_map_equiv,Equiv.symm_symm,mem_product,mem_univ,true_and] at hi
      let p:= pennant H i; let θ:= spin p.1; let v:=θ.symm x
      have hg:= u p.2 hi v h; change Finset.image θ (Beam.contents H P p.2).support⊆ _; intro j hj
      obtain ⟨k,hk,rfl⟩:=mem_image.mp hj
      have he : Lattice.separation x (θ k)=Lattice.separation v k:= by
         rw [show x=θ v from (θ.apply_symm_apply x).symm]; change Lattice.separation (p.1.1.act v+p.1.2) (p.1.1.act k+p.1.2)=_
         rw [separation_translate,separation_signed]
      exact (neighbors_mem ..).mpr (he.trans_le ((neighbors_mem ..).mp (hg hk)))
end cut
end YM.RG01Estimate.Caddy
