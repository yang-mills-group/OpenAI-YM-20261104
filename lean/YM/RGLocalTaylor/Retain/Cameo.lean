import YM.RGLocalTaylor.Retain.Vault
/-! # Real local response at one E markless letter: principal error price
BEAM receipt in inherited unmarked print. No assumed payment until
 normalization and schedule. Correction ESTIMATE only. At λ.V compared on
 true H with any Fα prediction.T.Pay zero for submitted stencil− physical
 moment − TEST transfer Φ at principal, all derivatives after assembly in
 actual reader book on applicable transports. TEST isn't physical model.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt RG01.Survive
open Mayer goodK Mill
open Match Song Push AnalyticBridge VerifiedReset Collection Extra.Iteration Refrain Geo Quotes
open Captain Ursell Gas Brim
open Fort
namespace Gorge
variable {f' f₁ f₂ : Post.glyph G f} {M:ℕ} (H) (X :Cash W s μ L Q o C T (impulse R f₂ a))
    {Ξ : Utopia H j v d r C' χ} {N : Captain H j C' d v Y A b r B q n χ}
    (p : BudgetPoint)
    (i : ℕ)

local notation "κ" => Opacity.key S
set_option quotPrecheck false
local notation "p₀" => head i (S:=S)
local notation "h₀" => once H i
local notation "y_" => icon H i
local notation "hX" => once X i
local notation "yX" => icon X i
local notation "Ru" => R.activities.E
local notation "ψ" => Read.field (fun _ k=>k=1) (cover H (physical H M) (χ:=χ))
local notation "ϕ" => Read.field (fun _ k=>k=1) (cover H (mantle H f₁ M) (χ:=χ))

def iconOnly (H: Cash W s μ L Q o C T R)(f: H.fragrances→ Config G c→ℝ)(p:H.fragrances) : Config G c→ℝ:=if p ∈ Set.range (icon H) then f p else 0
def RPC (f₁:Post.glyph G f):H.fragrances→ Config G c→ ℝ := Function.extend (icon H) (fun i=> (mage H f₁ i).onLog H χ (head i)) 0
local notation "A'" => RPC H f₂ (χ:=χ)

lemma recognized : A' y_=(mage H f₂ i).onLog H χ p₀:= (Beam.icon_inj H).extend_apply _ _ i

variable (hT:M≥1) (hE:R.activities.E=f₁+f₂)(hs:p.threshold=Pressure.temp s)(hB:p.B=radiusB s)(hj:p.order≤j)
   {w v':ℕ→ℝ} (hv: dual H f₂ a w v')
include hv hE hT N
lemma echo : let z:= reachability (H:=H) y_
   let f:= (ψ - ϕ - RPC H f₂ (χ:=χ)) y_
   LocalOn z f ∧ GaugeInvariant f ∧ Measurable f ∧ ∀ V:Config G c,Healthy (Pressure.temp s) z V → Ore V f v 0 j:= by
   intro z f; unfold f; let t':Orders M:=⟨1,by omega⟩
   rw [Pi.sub_apply,Pi.sub_apply,recognized, lonely H _ i _ t' (fun _=>Iff.rfl),lonely H _ i _ t' (fun _=>Iff.rfl),unSeal H i _ _ hT rfl,unSeal H i _ _ hT rfl,nameCore H _ _ _ hT,real_head H i hv.size _ hT]
   have h fU (hU : Fits H fU (H.supportP (κ i)) j) : Fits H fU (H.unionP p₀) j:= by rw [concern,← Brim.caption]; exact hU
   have ht fU (ht:Fits H fU (H.unionP p₀) j) : Measurable (Insert.onLog fU H χ p₀) ∧ GaugeInvariant (Insert.onLog fU H χ p₀) ∧ LocalOn z (Insert.onLog fU H χ p₀):= by
      refine ⟨ht.log_seam.2,Insert.onLog_invariant fU p₀,?_⟩
      rw [show z=H.unionP p₀ from (sites_icon H i).trans (concern H i).symm]; exact ht.log_seam.1
   have hP := h _ (fits_mage (j:=j) w hv.size i); have hf₁ := h _ (insulation (j:=j) H i hv hE); have hf₂ := h _ (force_m (j:=j) H i hv)
   obtain ⟨hr₁,hr₂,hr₃⟩:=ht _ hP; obtain ⟨h₁,h₂,h₃⟩:=ht _ hf₁; obtain ⟨h'₁,h'₂,h'₃⟩:=ht _ hf₂
   refine ⟨fun g U h=> congr_arg₂ (·-·) (congr_arg₂ (·-·) (hr₃ g U h) (h₃ g U h)) (h'₃ g U h),fun g U=> congr_arg₂ (·-·) (congr_arg₂ (·-·) (hr₂ g U) (h₂ g U)) (h'₂ g U), (hr₁.sub h₁).sub h'₁,fun V he E _ _ _ U x hx hZ=>?_⟩
   apply Brush.zi _ le_rfl zero_le_one
   -- mode from Captain body (TRUE). re-expression addition only at germ.
   have hv : Healthy (Pressure.temp s) (H.unionP p₀) (U x):=(by rw [hx,← show z=H.unionP p₀ from (sites_icon H i).trans (concern H i).symm]; exact he)
   filter_upwards [Fits.sumTwoGerm (Ξ:=N) hf₁ hf₂ h₀.2.2 hZ hv] with y hy
   rw [← Fort.add_m,← hE] at hy; dsimp only [Function.comp_apply,Pi.sub_apply,Pi.zero_apply] at *; rw [hy]; ring
include hs hj hB
local notation "F" => (ψ-ϕ-A')
lemma shape_coin : Film p (ψ-ϕ - RPC H f₂ (χ:=χ)) 0:= by
   let t:=F; refine ⟨fun _=>0,fun i=>?_,fun i=>?_⟩
   · simp [SumBudget]
   by_cases hz:i∈Set.range (icon H)
   · obtain ⟨i,rfl⟩:=hz; obtain ⟨ht,hM,hL,hV⟩:= Gorge.echo (N:=N) H i hT hE hv
     have hS: Sailor G p.threshold q j:= by rw [hs]; exact ⟨fun c g hb=> N.weigh.stroke c g (hb.trans N.talent)⟩
     simpa only [mul_zero] using! Mill.regularTop (icon H i) p hs hj (k:=p.power) le_rfl hB q N.income hS N.near N.position ht hL hM hV (he:=le_rfl)
   rw [Pi.sub_apply, Pi.sub_apply,Gorge.one_supported H (fun _ k=>k=1) f₁ hz (fun n h=>(h: n=1).le), sub_self, RPC, extend_apply' _ _ _ hz]; change p.Regular (reachability i) ((0:Config G c → ℝ)-0) ∧ ∀ x∈ reachability i, p.supBounds x _ (0-(0:Config G c→ℝ)) 0; rw [sub_zero]; exact ⟨CouplingShape.reg_const _,fun x hx=> VerifiedReset.sup_le (CouplingShape.sup_const _) (abs_zero (α:=ℝ)).le⟩ -- Lean parse change second 0
local notation "X'" => (impulse R f₂ a)
local notation "AX'" => Read.field (fun _ b=> b=1) (cover X (physical X M) (χ:=χ))

omit hv hE hs hj hB N
lemma projected {J : Rep G f}{U' : Cash W s μ L Q o C T J}(Φ : Match.Alliance U' H 1 0)(φ' : Match.Alliance U' X 1 0)
   (hp:Φ.units=Equiv.refl _)(hφ:φ'.units=Equiv.refl _)(ha:a≠0)(hv:shelved X v'):
   Gorge.stencil Φ A'=a • (Gorge.stencil φ' (iconOnly X (Read.field (fun _ b=> b=1) (cover X (physical X M) (χ:=χ))))) := by
   ext i V; rcases i with i|i
   · let t(i:U'.fragrances):= φ'.furrow i; let u i:=Φ.furrow i
     change (-1:ℝ)* A' _ V=a*((-1:ℝ)* ((if t i∈Set.range (icon X) then (AX' (t i)) else (0:Config G c→ℝ)) V))
     by_cases hx:i∈Set.range (icon U')
     · obtain ⟨i,rfl⟩:=hx
       have hv : (t (icon U' i))=(icon X i):= Beam.mimics U' φ' hφ i
       rw [hv,if_pos (Set.mem_range_self _),Beam.mimics U' Φ hp,recognized,← line_transport H X i (M:=M) ‹shelved ..› hT ha,Pi.smul_apply,smul_eq_mul]; ring
     have hv : t i ∉ Set.range (icon X):=by
        rintro ⟨u,hu⟩; exact hx ⟨u,φ'.furrow.injective ((Beam.mimics U' φ' hφ u).trans hu)⟩
     have hp': Φ.furrow i∉ Set.range (icon H):= by rintro ⟨u,hu⟩; exact hx ⟨u,Φ.furrow.injective ((Beam.mimics U' Φ hp u).trans hu)⟩
     unfold RPC; rw [extend_apply' _ _ _ hp',if_neg hv]; simp only [Pi.zero_apply,mul_zero]
   exact (smul_zero a (M := ℝ)).symm -- check args
end Gorge
end Retain
end YM.RGLocalTaylor
