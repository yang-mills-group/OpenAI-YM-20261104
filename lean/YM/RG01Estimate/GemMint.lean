import YM.RG01Estimate.Epicks
/-!
 # Anchored kin book moves across periodic charts. Receipts for E* exact
 from Deck.V maps; any Countable links.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Song
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{Γ: Type}{c f C F L'': Side}{P: Patch}{M D':ℕ}{K:Teller G}
section plans
variable {S:StepData c f}{T:Tube G S}{R: RG.Rep G f} {ρ W a u:ℝ}
variable {X:ConnectedActivityE6.Target G K}{o:ConnectedActivityE6.Target.Order G W}
    (I: Cash W ρ a L'' X o u T R)(Q:Lex Γ f)(m:ℕ)

-- finite buckle through a field-halo model cut. Need existence exhaustive selections eventually. no period bound on index.
def caps (V:Finset Γ)(k:ℕ): Finset (Header Γ c f):= (univ ×ˢ V).disjSum (Meadow.tuck k)
lemma parks (V:Finset Γ)(k:ℕ): { i:flagraph I Q m| ∀ j,i.val.2 j⊆ caps V k}.Finite:= by
   let u:Finset (Header Γ c f):= caps V k; let a i:=Fintype.piFinset (fun _ : Option (Fin i)=> u.powerset)
   let Y:Finset (Sons Γ c f):= (Finset.range m).sigma a
   apply Set.Finite.subset (Y.finite_toSet.preimage (@Subtype.val_injective _ _|>.injOn)); intro i hi
   change i.val∈ Y; apply mem_sigma.mpr; refine ⟨mem_range.mpr (Nat.lt_of_succ_lt (show _ from i.property.count)),?_⟩; apply Fintype.mem_piFinset.mpr; exact fun j=> Finset.mem_powerset.mpr (hi j)

def titleQ (V:Finset Γ)(k:ℕ) := (parks I Q m V k).toFinset
lemma cents (z:flagraph I Q m)(V:Finset Γ)(k:ℕ): z∈ titleQ I Q m V k↔ ∀ j, z.val.2 j⊆ caps V k := Set.Finite.mem_toFinset ..
lemma retiring (V:ℕ→ Finset Γ)(hv:∀ x, ∀ᶠ k in atTop, x∈ V k) (Z: flagraph I Q m): ∀ᶠ k in atTop, Z ∈ titleQ I Q m (V k) k:= by
   have ht i : ∀ᶠ k in atTop,Z.val.2 i ⊆ caps (V k) k:= (eventually_all_finset _).mpr (fun i _=> by
       rcases i with ⟨x,z⟩|i
       · exact (hv z).mono fun k hk=> Finset.inl_mem_disjSum.mpr (mem_product.mpr ⟨mem_univ _,hk⟩)
       exact (eventually_ge_atTop (Meadow.held i)).mono fun k hk=> Finset.inr_mem_disjSum.mpr ((Meadow.pocket k i).2 hk))
   exact (eventually_all.mpr ht).mono fun i hi=>(cents ..).2 hi

def garnet (χ : Chi) (V: Finset Γ)(k:ℕ) (x : Site c) (U: Config G c):= ∑ i∈ (titleQ I Q m V k).filter (fun i=>x∈ arborX I Q i.val),
     -((arborX I Q i.val).card:ℝ)⁻¹ * stream I χ U (cask I Q m i)

def aspect (χ: Chi)(y : ℝ)(V : Finset Γ)(k:ℕ):= Meadow.atlas (garnet I Q m χ V k+Meadow.garner T.down T.low R.beta y (radiusB ρ) k)
lemma reflections (χ: Chi)(y:ℝ)(V:Finset Γ)(k:ℕ) : Trio.Mirrors (aspect I Q m χ y V k):= fun x v b U => Meadow.astrolabe _ x U (v,b)
end plans

section links
variable {h : f.val=c.val*P.L.val}{H:F.val=C.val*P.L.val}{Q: KernelChoices}{hC:C.val=c.val*M}{he:2≤c.val} {p u w W v:ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T:Tube G (stepped Q h)}{T':Tube G (stepped Q H)}{R:RG.Rep G f}{R':RG.Rep G F}{V:Lex Γ f}{V': Lex Γ F}
    (hT:T'=re T)(hr:R'.p=R.p)(hz:R'.beta=R.beta)
    {X:ConnectedActivityE6.Target G K}{o:ConnectedActivityE6.Target.Order G W}
variable (hp:R'.path=R.path) (I : Cash W p u L'' X o v T R) (I' : Cash W p u L'' X o w T' R') (A: Charts (h:=h) (H:=H) hC he R R' V V')
   (x:Site C) {d Z m n:ℕ} (hQ: StageMask R (stepped Q h) V d)(hW:StageMask R' (stepped Q H) V' d)(hZ:4*(house X.halo (radiusB p) d m+optic X.halo (radiusB p) d+5)<c.val)
local notation "B" => radiusB p
local notation "p'" => optic X.halo B d
local notation "D" => house X.halo B d m
local notation "x'" => (Macrame.splitter (Deck.divides hC) x)
variable {b ℓ j i : ℕ} {C' d' z T'' A' B' r V'' u' s₁ a' b' c' X' e' D'' T₀ q' :ℝ} {χ:Chi}
   (N : Captain I b C' d' z T'' A' B' r V'' u' i χ) (N' : Captain I' j s₁ a' b' c' X' e' D'' T₀ q' ℓ χ)
   (f' : Config G c) (hV: RG.flags (Pressure.temp p) f'= ∅)
lemma staged (V: Finset Γ)(k:ℕ)(i:Header Γ C F): i∈ caps V k ↔ warps (L) i∈caps V k:= by
    rcases i with ⟨i,j⟩|i
    · simp only [caps, Finset.inl_mem_disjSum,mem_product,mem_univ,true_and]; unfold warps; simp only [Sum.map_inl,inl_mem_disjSum, mem_product,mem_univ,true_and]; rfl
    unfold warps caps; simp only [Sum.map_inr,inr_mem_disjSum, Meadow.pocket]; rcases i with i|i|i|i<;> rfl
include hT hr hz I I' N N' hV hp A hW hZ
set_option maxHeartbeats 300000 in
lemma surgery (Z:flagraph I' V' m)(W : flagraph I V m) (hh:x∈arborX I' V' Z.val) (hs: follows (L) Z.val=W.val):
    let f:=cask I V m W; let f₁:= cask I' V' m Z; let U:=(L).low.links f'
    ((arborX I V W.val).card=(arborX I' V' Z.val).card) ∧ stream I' χ U f₁= stream I χ f' f:= by
   have hf := within I' V' m hW x Z.property hh
   intro f f₁ U; constructor
   · rw [← hs, cross hp I I' A]; exact card_image_of_injOn ((Meadow.garden hC x (show 2*D<c.val from by omega)).mono (coe_subset.mpr hf))
   have hc: RG.flags (Pressure.temp p) U=∅:= by ext i; rw [show i∈RG.flags (Pressure.temp p) U↔_ from Deck.flagged hC f' i (show c.val>4 from (by omega)) (Pressure.temp p),hV]; simp
   have ht : stream I χ f' f= I.trainedPool χ f' f:= Eq.symm ((congr_fun (N.permitAverage f).2.2.2.1 f').trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hV]; simp)))
   have hx : stream I' χ U f₁= I'.trainedPool χ U f₁:= Eq.symm ((congr_fun (N'.permitAverage f₁).2.2.2.1 U).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [hc]; simp)))
   rw [ht,hx]; obtain ⟨j,Hj⟩:=W; dsimp only at hs; subst j
   unfold Cash.trainedPool Gas.term; apply congr_arg₂ HDiv.hDiv _ rfl; apply congr_arg₂ HMul.hMul
   · exact (radiant I' V' m Z.val Z.property).symm.trans ((parity hp I I' A x hW Z.val (Z.property).hot (show 2*D < c.val by omega) hf).trans (radiant I V m _ Hj))
   apply prod_congr rfl; intro i _
   let pH:=p'; have hu:∀ z:Site _ × Γ, regularFoot (decreed H) 0 B R' (V' z) ⊆ neighbors pH ((decreed H).parent z.1):= by
      intro z; apply (stores_high V' hW (lt_of_lt_of_le (by norm_num) I'.laws.data.room.sight.1) z 0).trans
      intro x hi; apply (neighbors_mem ..).mpr; apply ((neighbors_mem ..).mp hi).trans
      unfold pH optic Mint.width; omega
   exact spawn_read I' I hp hr hz A x (D) (by omega) (woven I' x hW (by omega) _ Z.property hh i)
        ((patio I' V' Z.val _).trans hf) ((Z.property.hot i).vote) hu (by unfold pH; omega) hT f' χ hV ((Z.property.hot i).active) (Hj.hot i|>.active) -- size depends proof

include hQ
lemma crowns (V₀:Finset Γ)(k:ℕ) : Evoc.garnet I' V' m χ V₀ k x ((L).low.links f')= Evoc.garnet I V m χ V₀ k x' f':= by
    let π:= titleQ I V m V₀ k; let p:=titleQ I' V' m V₀ k
    let s':= π.filter (fun i=> x'∈ arborX I V i.val); let t:= p.filter (fun i=> x∈ arborX I' V' i.val)
    have hu i (hi:i∈t):= orders hp I I' A x hW (show 2*D < c.val by omega) i.val i.property ((mem_filter.mp hi).2)
    let f (i:flagraph I' V' m) (h:i∈t): flagraph I V m:=⟨follows (L) i.val,(hu i h).1⟩
    have hv i z (hk:(i:flagraph I V m).val=follows (L) (z:flagraph I' V' m).val): i∈π ↔ z∈p:= by
       unfold π p; rw [cents,cents,hk]; constructor
       · intro H w a hb; exact (staged V₀ k a).mpr (H w (show warps (L) a∈ _ from Finset.mem_image_of_mem (warps (L)) hb)) -- he inference
       intro H w a ha; obtain ⟨i,hi,rfl⟩:=mem_image.mp ha; exact (staged V₀ k i).1 (H w hi)
    apply Finset.sum_bij f (fun i hi=>mem_filter.mpr ⟨(hv _ i rfl).mpr (mem_filter.mp hi).1,(hu i hi).2⟩) ?_ ?_ ?_
    · intro i hi j hj hq; apply Subtype.ext; apply picks I' x hW (by omega) i.val j.val i.property j.property (mem_filter.mp hi).2 (mem_filter.mp hj).2 (congr_arg Subtype.val hq)
    · intro i hi
      obtain ⟨a,hA,hZ,hF⟩:= Evoc.patch hp I I' A x hQ hW (show 2*(D+p')<c.val by omega) i.val i.property ((mem_filter.mp hi).2)
      refine ⟨⟨a,hA⟩,mem_filter.mpr ⟨(hv _ _ (show _=(follows (L) (⟨a,hA⟩ : flagraph I' V' m).val) from hF.symm)).1 ((mem_filter.mp hi).1),hZ⟩,Subtype.ext hF⟩
    intro i hi; obtain ⟨hw,H'⟩:=surgery hT hr hz hp I I' A x hW hZ N N' f' hV i (f i hi) ((mem_filter.mp hi).2) rfl
    rw [hw]; exact congr_arg₂ _ rfl H'

lemma thrill (V₀:Finset Γ)(k:ℕ)(γ:ℝ) : Evoc.aspect I' V' m χ γ V₀ k x ((L).low.links f')= Evoc.aspect I V m χ γ V₀ k x' f':= by
   let b (θ:Seat c):=garnet I V m χ V₀ k ((Meadow.spin θ).symm x') (θ.view f') + Meadow.garner T.down T.low R.beta γ B k ((Meadow.spin θ).symm x') (θ.view f')
   unfold aspect Meadow.atlas; change _=likely b
   rw [← Meadow.revolving hC b]
   apply congr_arg likely; funext θ
   simp only [b,Pi.add_apply]; rw [show θ.view ((L).low.links f')=(L).low.links ((Meadow.pinch hC θ).view f') from Meadow.estuary hC f' θ]
   apply congr_arg₂ HAdd.hAdd
   · rw [← Meadow.inverts hC θ]; exact crowns hT hr hz hp I I' A _ hQ hW hZ N N' ((Meadow.pinch hC θ).view f') (Meadow.covers_field (Meadow.pinch hC θ) f' hV) V₀ k
   rw [hz,← Meadow.inverts hC θ]; subst T'; exact Meadow.garner_pack hC ..
end links
end YM.RG01Estimate.Evoc
