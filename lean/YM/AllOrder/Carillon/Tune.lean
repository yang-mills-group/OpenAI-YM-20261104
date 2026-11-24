import YM.AllOrder.Carillon.Tread
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Carillon
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "B" => radiusB p
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)
open Rosary High Marlin Progress.DirectedRecipe Trio Slide Ovens
-- used physical minus model root reading. General Offer κ.H.Group.
variable (F:Finset H.fragrances) (χ:Chi) (p':BudgetPoint)(β γ:ℝ)(M:Burn.Locale G)
local notation "V!" => M c
local notation "Γ"=> organ H χ β γ
local notation "P0"=> Beam.marquee H p'
local notation "Y"=> centerC F χ k β γ
abbrev Lum (k:ℕ) : Offer G c:= centerC F χ k β γ-M c
variable {D:Stars→Side} {w r:ℕ} (Q:∀ i:Stars,(D i).val=2*(w+i.val)) (z:ℕ) (fa:∀ i:Stars,Offer G (D i)) (U: Config G c) -- B moment pack independent.Need lint variable name collision
abbrev trueM (p:BudgetPoint)(M:Burn.Locale G)(o:Site c)(U:Config G c):= masked p.threshold (Till.court o p.B) (M _ o) U
local notation "X₀"=> Lum F χ β γ M k
local notation "M₀"=> trueM p' M
local notation "𝓟"=> posting p' H
def loss (k:ℕ)(x:Site c)(U:Config G c):= usedC F χ p' β γ k x U-trueM p' M x U-Lum F χ β γ M k x 1 - unearned p' Q z (Trio.rip fa) x U
local notation "q"=> loss F χ p' β γ M Q z fa k
local notation "O"=> ornament Q fa
local notation "P₁"=> Listing.read P0 (linger F χ k β γ)
variable {V v C:ℝ} (h:Collection.Local (posting p' H) p' (organ H χ β γ) V v)
    (hw:Trio.Mirrors (M c))(hp:∀ x:Site c,Till.Fairness p' x (Till.court x p'.B) (M c x) C)
lemma entwines (hw:Trio.Mirrors (M c)):Trio.Mirrors X₀:= by intro x s b U; simp only [Lum,Pi.sub_apply,newC_turns F χ k β γ x s b U,hw ..] -- implicit
include h hw
lemma artifact (U:Config G c) : (Listing.read 𝓟 Γ).additive p' U=(P₁).additive p' U+(Fintype.card (Site c):ℝ)* (X₀) 0 1+(∑ i,trueM p' M i U)+ (∑ i,masked p'.threshold (neighbors z i) (ornament Q fa i) U)+ ∑ i:Site c,q i U:= by
    let f:= X₀; let x:= f 0 1
    have hv : ∀ j: Site c, X₀ j 1=x:= by
       intro i; rw [show i=Lattice.affine 1 i (0:Site c) from (by simp [Lattice.affine]),← entwines F χ β γ M hw]; rw [pull_one]; change X₀ 0 (Lattice.translate i 1) = _; rfl
    let v j:= usedC F χ p' β γ k j U; have he:= sparedC (k:=k) F χ p' h U; have hp: ∑ i∈ foliage F k, masked p'.threshold (P0|>.reg i|>.support) ((Γ).logRead i) U=∑ j:Site c,v j:= by
       unfold v usedC; rw [sum_comm]; symm; refine sum_congr rfl ?_; intro i hi; rw [← sum_mul, Meadow.paysOne,one_mul]; rfl
    rw [he,hp]; unfold ornament; rw [parade]; simp_rw [loss,hv,sum_sub_distrib]; rw [sum_const, card_univ,nsmul_eq_mul]; unfold v; ring -- f order
omit hw
section census
include hp
variable {l:ℕ} (hBod:p'.B=Pressure.radiusB p) (hc0 : ∀ i∈F,∀ x∈perf H i,perf H i⊆neighbors r x) (hop : Pressure.radiusB p + Pressure.radiusB p ≤ r) (u:Site c)
include hBod hc0 hop
lemma trueHealthy (o:Site c): Till.court o p'.B⊆ neighbors r o:= by intro x hx; apply (neighbors_mem ..).2; refine le_trans (b:=p'.B) ?_ (by omega); obtain ⟨y,hy,h⟩:= halo_spec.mp hx; exact (mem_singleton.mp hy) ▸ h
lemma percolate (hq : ∀ i j,p'.Regular univ (fa i j)) (hw:w+4 ≤ z) (he:r≤l)(hK:2*z≤l): Tidy p' (neighbors l u) (q u):= by
    let X:=neighbors l u; let V:= M₀ u; refine tidy_sub p' (u:=(usedC F χ p' β γ k u-V)-fun _=>X₀ u 1) (v:= Trio.unearned p' Q z (rip fa) u) (tidy_sub _ (tidy_sub _ (tidy_occasionC F χ p' β γ hBod hc0 hop u h.smooth he) ?_) (tidy_const ..)) (tidy_sum _ _ _ _ fun i _=> tidy_scale _ _ (tidy_sum _ _ _ _ fun j _=> tidy_mask _ (unit_m p' Q z fa hq hw (emerge Q i j u) i j) (Trio.patch Q z hw i j u hK)))
    apply tidy_mask p' (X:= Till.court u p'.B) (hp u|>.ready); intro x hx; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((trueHealthy F χ p' β γ M h hp hBod hc0 hop _) hx)).trans he -- .. placeholders
-- use lemma caller.Proof cancellation when Healthy moves.Packs
lemma cool (s:Site c) (hz:2*z≤l) (h:r ≤ l) (hw:w+4≤z)(hp':2*r≤w) (hc:4*r+16≤c.val)(hT:0<r) (he:CompatibleP p' r (Lum F χ β γ M k) fa)(hV : Healthy p'.threshold (neighbors l s) U): q s U =0:= by
 let u:= U; have hv : usedC F χ p' β γ k s U=Y s U:= by
    unfold usedC; rw [newC_bound_frame F χ p', Finset.sum_apply]; refine sum_congr rfl fun i hi=>?_; by_cases hx:Meadow.garnerAt H p' s i=0; · rw [hx]; simp
    have hv:= artists F p' hBod hc0 hop s i hi hx; exact congr_arg (Meadow.garnerAt H p' s i * ·) (masked_eq _ _ ((Γ).logRead i) _ (hV.mono_left (show ((P0).reg i).support ⊆ neighbors l s from (fun j hj=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (hv.2 hj)).trans h)))))
 have he':trueM p' M s U=M _ s U:= masked_eq _ _ _ _ (hV.mono_left (show Till.court s p'.B ⊆ neighbors l s from ?_)); swap;
 · intro z hz; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((trueHealthy F χ p' β γ M ‹Collection.Local _ p' _ V v› hp hBod hc0 hop _) hz)).trans h -- fix
 have hh:=Trio.cruising p' Q z (rip fa) U s hw hp' hz hc hV (fun i=> Boulevard.stillA (X₀ i)) (tinted X₀ _ he) hT
 unfold loss; rw [hv,he',hh]; exact sub_self _
lemma safety (f : Stars→ℝ) (hq:∀ i (V:Config G (D i)), flags p'.threshold V=∅→∀ x, ‖fa i x V‖ ≤ f i) (hZ:w+4 ≤ z) : ‖q u U‖ ≤ ((ballCost r:ℝ)*V+C) + (ballCost r:ℝ)*V +∑ i:Stars,|Slide.ray i| * ((Fintype.card (Site (D i)):ℝ)*(f i+f i)) := by
  have he := Trio.stipends p' U Q z fa _ hq hZ u; have hh: ‖X₀ u 1‖ ≤ (ballCost r:ℝ)*V:= by
     simp only [Lum,Pi.sub_apply,(hp u).one, sub_zero]; exact chamber_valueC F χ p' β γ _ hBod hc0 hop u h (UVNext.CouplingReset.flags_one ..) -- ..
  have hf: ‖(M₀ u U)‖ ≤ C:= CouplingShape.mask_cost (hp u|>.cap) _
  exact (norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (liftsGC (k:=k) F χ p' β γ U hBod hc0 hop u h) hf)) hh)) he)
end census
end YM.AllOrder.Carillon
