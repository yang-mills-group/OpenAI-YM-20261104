import YM.LocalTaylorR2.Marigold.Merchant
import YM.LocalTaylorR2.Grafting.Truss
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rising
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
variable {b B ρ q:ℝ}{a d a' : H.ThinP→Orders l→ℝ}{σ σ':H.ThinP→ℝ}
-- avoid naming clashes sigma universal
variable {k₁ :ℝ} (h:Mind H M χ l v₀ j a a' σ ρ k₁) (z:H.fragrances) (take:H.fragrances→ℕ→Prop)
variable (ψ:Reel.Strand→ Copper.Stems T)
open LeafReady

open Reel
section money
variable {d':ℝ}{ξ b₀ γ:ℝ}(N:Captain H j C' d' v₀ w A b r b₀ ξ n χ)
variable (m₀:ℕ)
variable (QF:∀ i:LogIndex c f, Filled (Pop H (H.supportP (identityLog i))) 1 Reel.Strand.dial (fun j=> ψ j i))
include QF N
lemma hasCharge (p:H.ThinP)(q:Orders l) (W:Config G c)(hw: Healthy (Pressure.temp x) (H.unionP p.val) W)(he:q.val ≤ l): Filled ⊤ q.val Reel.Strand.dial (fun i=> memo W (mintC H χ (ψ i) p q)):=by
   let T₀:=p.val; let A:= H.unionP p.val; let X:= Pop H A
   by_cases h : live H p; swap; · unfold mintC; simp_rw [if_neg h]; exact Filled.steady _ Submodule.mem_top
   have hz : q≠ Candle.perch l:= by intro h; rw [h] at he; change l+1 ≤ l at he; omega
   let Y i (j:Paint T₀ l):= episode H χ p.val (Copper.namesP (ψ i) j); let C:= univ.filter fun k:Paint T₀ l=> chooseSlot k=q
   have hx: (fun i=> memo W (mintC H χ (ψ i) p q))=∑ j∈ C,(fun i=>memo W (Y i j)):= by
      ext1 i; rw [Finset.sum_apply, ← map_sum]; apply congr_arg; ext V; rw [mintC, if_pos h,Finset.sum_apply]; rfl
   rw [hx]; apply Filled.group; intro i hi; have hP:chooseSlot i=q:= (mem_filter.mp hi).2; have ht := ne_of_eq_of_ne hP hz
   have hp: Filled X (inserts i) Reel.Strand.dial (fun q=> Copper.namesP (ψ q) i):= Orbit.frost H Strand.dial ψ QF (H.unionP p.val) (Subset.refl _) i ht
   have hI := Reel.pendulum N W hw p.2.2 hp; apply hI.onward
   have hb₀:min (l+1) (inserts i)= q.val:= congr_arg Fin.val hP
   omega
lemma titan (p:H.ThinP)(q:Orders l) (W:Config G c)(hw: Healthy (Pressure.temp x) (H.unionP p.val) W)(he:q.val ≤ l): Filled ⊤ q.val Reel.Strand.dial (fun i=> memo W (dream M H p χ (ψ i) q)):=by
   let T₀:=partners M p.val; let A:= H.unionP p.val; let X:= Pop H A
   by_cases h : lush M H p; swap; · unfold dream; simp_rw [if_neg h]; exact Filled.steady _ Submodule.mem_top
   have hz : q≠ Candle.perch l:= by intro h; rw [h] at he; change l+1 ≤ l at he; omega
   let Y i (j:Paint T₀ l):= episode H χ p.val (betide M H p (ψ i) j); let C:= univ.filter fun k:Paint T₀ l=> chooseSlot k=q
   have hx: (fun i=> memo W (dream M H p χ (ψ i) q))=∑ j∈ C,(fun i=>memo W (Y i j)):= by
      ext1 i; rw [Finset.sum_apply, ← map_sum]; apply congr_arg; ext V; rw [dream, if_pos h,Finset.sum_apply]; rfl
   rw [hx]; apply Filled.group; intro i hi; have hP:chooseSlot i=q:= (mem_filter.mp hi).2; have ht := ne_of_eq_of_ne hP hz
   have hp: Filled X (inserts i) Reel.Strand.dial (fun q=> betide M H p (ψ q) i):=by
      let A₁:=stems M H; have HA: A₁∈X:= (stemTest M H).mono (sees_set M H h.1); let B':= Reel.Strand.dial
      have hh := Orbit.frost H B' ψ QF (H.unionP p.val) (enough M H (p:=p)) i ht
      convert (Filled.steady (n:=0) A₁ HA).times (U:=Pop H A) hh (· * ·) (fun _ x _ y=> Kept.times x y) (fun _ _ _=> add_mul ..) (fun _ _ _=> mul_add ..) (popPow H) using 1
      rw [zero_add]
      rfl
   have hI := Reel.pendulum N W hw p.2.2 hp; apply hI.onward
   have hb₀:min (l+1) (inserts i)= q.val:= congr_arg Fin.val hP
   omega
variable (hB:∀ i,take z i→i≤ m₀)(hx:m₀≤l) (δ:BudgetPoint) (he:δ.threshold=Pressure.temp x)
include hB hx

include he
lemma orangeB (o:Site c)(U:Config G c)(hU:Healthy δ.threshold (locus M H o z) U): Filled ⊤ m₀ Reel.Strand.dial (fun i=> memo U (routeP M H z take (ψ i) χ l)):= by
   by_cases h:speaks M H z; swap; · simp_rw [gooff _ _ _ _ _ _ _ h]; exact Filled.steady _ Submodule.mem_top
   unfold locus at hU; rw [if_pos h,he] at hU
   let S₀:= Option (Fin z.1); let F':= Strand.dial; let w (j:S₀) (i:Strand):= sennet M H z (ψ i) χ l j
   let f (j:S₀)(q:S₀→Orders l) (i:Strand):= ∏ k,w j i k (q k); let K:= univ.filter fun q=> take z (atGrade (z:=z) (M:=l) q)
   let x:ℝ:=coefficient H.seam z.snd/↑(z.1+1).factorial; let g i:=routeP M H z take (ψ i) χ l
   have hp : memo U ∘ g = (x • ∑ j,(∑ q∈K,(fun i=>memo U (f j q i)))):= by
      ext1 i; rw [Pi.smul_apply,Finset.sum_apply]; simp_rw [Finset.sum_apply, ←map_sum]; rw [← Reel.memoScale]; apply congr_arg (memo U); funext v
      unfold g routeP f; simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.prod_apply]; unfold x S₀ w K Products.filtered Products.atGrades; congr!
   change Filled _ _ _ (memo U ∘ g); rw [hp]; refine Filled.scaling (Filled.group _ _ (fun j _ => Filled.group _ _ (fun q hq=>?_))) x
   let u₀ k:= (q k).val; have ht: (∑ k: S₀,u₀ k)≤ m₀:= hB _ (mem_filter.mp hq).2
   apply Filled.onward _ ht; unfold f; simp_rw [map_prod]
   rw [show (fun i=>∏ k:S₀,memo U (w j i k (q k))) = ∏ k,(fun i=> memo U (w j i k (q k))) from funext fun i=> (by rw [Finset.prod_apply])]
   refine Filled.accumulate _ _ _ (fun k hk=>?_) Submodule.mem_top (fun _ _ _ _=>Submodule.mem_top) (scalar_prod U)
   have hy:= ((Finset.single_le_sum (f:=u₀) (fun _ _=>Nat.zero_le _) hk).trans ht).trans hx
   have hz:= Orbit.scopeFlag H z U hU k; unfold w sennet tangle; split
   next=> exact titan M H ψ N QF _ _ U hz hy
   next=> exact hasCharge H ψ N QF _ _ U hz hy
end money
end YM.LocalTaylorR2.Marker
