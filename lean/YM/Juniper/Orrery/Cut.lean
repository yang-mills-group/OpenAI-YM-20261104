import YM.Juniper.Flare.Dressed
/-!
 # Neighborhood cutoff (post-estimator pruning)

 On E MODEL ONLY; do not erase true x field. Chosen by true support
 and site at its scale and auxiliary; works with arbitrary seat projections
 in a Charm (so no name condition on rotation in the estimators).
 Before paying, transfer through `Flare.Carved`, then read in full prior
 supports to propagate. Here only transfer and mildness, price in following files.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Orrery
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Progress.DirectedRecipe UVExtension Height
open Ovens Ovens.Pipes Whirl Tabernacle Dales Flare Deck.Mint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {c f:Side} {s b :ℕ} (B: BudgetPoint)
abbrev ShortF (s : ℕ)(i : RegularAddress c) := i.support ⊆ Animals.neighbors s i.site
variable (j:RegularAddress c)
lemma short_iff (s:ℕ) : ShortF s j ↔ j.support ⊆ halo s {j.site}:=by
   unfold ShortF; rw [show neighbors s j.site = halo s {j.site} from by ext i; rw [neighbors_mem]; simp only [halo_spec,mem_singleton,exists_eq_left] ]
lemma short_perm {i j:RegularAddress c}{q:Signed}{u:Site c}(hi : j.support=i.support.image (affine q u))(h : j.site=affine q u i.site) : ShortF s j ↔ ShortF s i:= by
   unfold ShortF; rw [hi,h]; constructor
   · intro hh k hk; refine (neighbors_mem ..).2 ?_; have he:= (neighbors_mem ..).1 (hh (mem_image_of_mem (affine q u) hk)); simpa [Lattice.affine] using he
   intro h' k hk; obtain ⟨i,hi,rfl⟩:= mem_image.mp hk; apply (neighbors_mem ..).2; simp only [Lattice.affine, separation_translate,separation_signed]; exact (neighbors_mem ..).1 (h' hi)
omit j
section prune
variable {ι : Type*} {b w:ℝ}
abbrev Payment (B:BudgetPoint)(Z:ι→RegularAddress c)(g:ι→ Config G c→ ℝ)(b:ℝ) := ∃ t:ι→ℝ,(∀ i,B.supBounds (Z i).site (Z i).support (g i) (t i)) ∧ Quotes.anchored B Z t b

def pris (s:ℕ)(Z:ι→RegularAddress c)(g:ι→ Config G c→ℝ):= fun i : ι=> if ShortF s (Z i) then g i else 0
def prune (s:ℕ)(H: Activities G c) : Activities G c:= { H with E:= pris s H.reg H.E }
variable {B} {ι : Type*} {Z:ι→RegularAddress c}{g:ι→ Config G c→ℝ}{H : Activities G c}
lemma minute (h:Payment B Z g b) : Payment B Z (pris s Z g) b:= by
   obtain ⟨u,hu,h⟩:=h; refine ⟨u,fun i=>?_,h⟩; unfold pris; split; exact hu i; exact VerifiedReset.sup_le (no_cost B _ _) (hu i).1
noncomputable def changes {t:Signed}{u:Site c}(h: H.Moves t u)(s:ℕ): (prune s H).Moves t u :=
   ⟨h.ep,h.kp,h.reg_site,h.reg_support,h.forced_support,h.forced_inventory,h.forced_tests,fun i U=> by
       simp only [prune,pris]; by_cases hi: ShortF s (H.reg i)
       · rw [if_pos hi, if_pos ((short_perm (h.reg_support i) (h.reg_site i)).2 hi)]; exact h.valuesE i U
       rw [if_neg hi, if_neg ((short_perm (h.reg_support i) (h.reg_site i)).not.mpr hi)]; rfl,h.valuesK⟩
lemma pruned (h:H.Valid B b w): (prune s H).Valid B b w:=by
   refine ⟨⟨fun i=>?_,fun i=>?_,fun i hi u v hu hv=>?_⟩,⟨h.forced.sym,h.forced.symtest,h.forced.meas,h.forced.meas_test,h.forced.reads,h.forced.reads_test,h.forced.permit⟩,fun t u=>⟨changes (h.moves t u|>.some) s⟩,minute h.boundE,h.boundK⟩
   · simp only [prune,pris]; split; exact h.regular.smooth i; exact unspent ..
   · simp only [prune,pris]; split; exact h.regular.at_flat i; rfl
   simp only [prune,pris]; split; exact h.regular.vanish i hi u v hu hv; exact VerifiedReset.hessian_zero 0 u v
lemma telescope (P:Ratio c f)(b l:ℕ)(H:Rep G f)(hB:0<b)(hs:s ≤ 2*b){i:ℕ}(hh: ShortF s (H.activities.reg i)) : Raw.regularFoot P l b H i ⊆ neighbors (Deck.Mint.width l b b) (P.parent (Flare.fanchor H i)):=by
   intro p hp; obtain ⟨x,hx,ht⟩ := halo_spec.mp (Footprint.inspected_price P l b (H.activities.reg i).support hB hp); obtain ⟨j,hj,rfl⟩:=mem_image.mp hx; apply (neighbors_mem ..).mpr
   have hz: separation (P.parent (Flare.fanchor H i)) (P.parent j) ≤ s+1:= (Work.E04.parent_separation ..).trans (Nat.add_le_add_right ((neighbors_mem ..).1 (hh hj)) _)
   apply (separation_triangle _ (P.parent j) _).trans; unfold Deck.Mint.width; rw [add_mul] at ht; omega
end prune
section compare
variable {b k:ℝ}{V W:ℕ→RegularAddress c}{v w:ℕ→ Config G c→ℝ}
variable {H: Flare.Carved V v W w}
lemma transfer (H: Flare.Carved V v W w)(hv: Payment B V v b): Payment B W w b:= by -- adapted Readdress.Ebound
   obtain ⟨h,hp,he⟩:= hv; refine ⟨stuff H.θ h,fun i=>?_,fun x=> transfer_budget H.θ ?_ ?_ (he x) ⟩
   · by_cases hi : i∈Set.range H.θ; · obtain ⟨p,rfl⟩:=hi; rw [H.align,H.keeps,stuffed]; exact hp _
     rw [H.forget _ hi,blank _ _ hi]; exact no_cost ..
   · intro i; rw [H.align, stuffed]
   intro i hi; rw [blank _ _ hi]; simp [BudgetPoint.mass]
omit B
noncomputable def entice (H:Flare.Carved V v W w) (s:ℕ) : Flare.Carved V (pris s V v) W (pris s W w) := by
   refine ⟨H.θ,H.align,fun i=>?_,fun i hi=>?_⟩
   · unfold pris; rw [H.align,H.keeps]
   unfold pris; rw [H.forget i hi]; split <;> rfl
noncomputable def deltaP (H:Flare.Carved V v W w) (s:ℕ) : Flare.Carved V (v-pris s V v) W (w-pris s W w):=
   ⟨H.θ,H.align,fun i=> congr_arg₂ (· - ·) (H.keeps i) ((entice H s).keeps i),fun i hi=>
      (congr_arg₂ HSub.hSub (H.forget i hi) ((entice H s).forget i hi)).trans (sub_self _)⟩
variable (s : ℕ) {L:Levels G} {m n:ℕ}{d:Cham L m n}(x y:Valve m n L d)
local notation "D"=> L.budget m
local notation "σ"=> L.clock.allowance m
local notation "T"=> Tabernacle.floor D
local notation "Z"=> L.S.side m n
local notation "Φ"=> drawer G Z|>.reg
local notation "J"=> (pris s (drawer G (L.S.side m n)|>.reg) (y.val.1))
noncomputable def shave : Valve m n L d := by
   refine ⟨(J,y.val.2),?_⟩; obtain ⟨⟨a,b,h⟩,g⟩:= d.income (D) y
   change Tabernacle.copied (D) d (J,y.val.2); refine ⟨⟨a,b,pruned h⟩,fun i t=>?_⟩
   obtain ⟨f,hv⟩:=g i t; exact ⟨changes f s,hv⟩
lemma shaved : (shave s y).val.1= J:= rfl
lemma saveK : (shave s y).val.2= y.val.2:= rfl
variable {s}
local notation "L₁"=> place L m n d
lemma easier (s:ℕ) : ‖L₁ (shave s y)‖≤ ‖L₁ y‖:= (Native.pay_total _ _).2 (pruned ((Native.pay_total y _).1 le_rfl))
variable {W!:ℕ→RegularAddress (L.S.side m n)}{w!:ℕ→ Config G (L.S.side m n)→ℝ}{C: Flare.Carved W! w! (drawer G (L.S.side m n)|>.reg) y.val.1}
include C
lemma shavedPay (h:Payment (D) (W!) (w!-pris s W! w!) (b*σ))(hb:0≤b): ‖L₁ y- L₁ (shave s y)‖ ≤ b:= by
   rw [Native.total_split y (shave s y)]; refine max_le ((Native.standard_le_emission y (shave s y) b hb).2 (transfer (D) (deltaP C s) h)) ?_; rw [show Native.trueK (shave s y)= Native.trueK y from rfl,sub_self,norm_zero]; exact hb
lemma erased (he : ‖L₁ x-L₁ y‖ ≤ k)(h : Payment (D) (W!) (w!-pris s W! w!) (b*σ))(hb:0≤b) : ‖L₁ x-L₁ (shave s y)‖ ≤ k+b:= by
   apply (norm_sub_le_norm_sub_add_norm_sub _ (L₁ y) _).trans; exact add_le_add he (shavedPay y (C:=C) h hb)
end compare
end YM.Juniper.Orrery
