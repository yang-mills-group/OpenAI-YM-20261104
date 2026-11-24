import YM.RGLocalTaylor.Retain.Payer
/-!
# First-layer budget and promoted LOG receipts
POINTED-response includes port on same activated features; preserves F allowances.
General enough for FORT plus with additional readers from real stencils.
Prove `.Pilot` using actual heat.J price.Cot. Uses factor 2 per molecule
in Second tree pass to absorb full differentiated E(t) count.
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt Blaze.March
namespace Retain
open RG01.Survive Mayer goodK Trees Merge Palette Fort Laminate
namespace Mill

variable {m M :ℕ} {p:Molecule S} {e vJ uJ K θ α β Z γ δ r' d' ρ:ℝ} {AΦ AΨ :Stencils T M}
   {Ξ : Utopia H j v d r C' χ} {g:Head S → ℝ}
   {N : Captain H j C' d v Y A b r B q n χ}
   (hG: Awning H N.conduit A b d' e uJ vJ k l)(h : Priced N.conduit M g θ ρ α A AΦ)
   (hT:vJ≤α)(hu : Quoted N.conduit M g θ ρ α A γ AΦ AΨ)

abbrev account (Q : ConnectedActivityE6.Target G P)(L:Side)(μ s:ℝ)(l:ℕ)(a:ℝ):= Reserves.extract Q.ε l 0 0*Reserves.treeYield (a* Fort.γprice Q L s μ) (1/2) 0
set_option quotPrecheck false
local notation "c!" => creditStencil M θ ρ
local notation "X₁" => Q.goal L s
local notation "X₂" => Fort.γprice Q L s μ
local notation "u₀" => speedBill e uJ α j
local notation "u₁" => account Q L μ s (l+j) c!
local notation "d!" => (Vbill H)
local notation "wₜ" => fun i p=> Vbill H i p g j l e uJ α (creditStencil M θ ρ)

variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (hw: ∀ i,0≤rA i)
abbrev promo (p:Molecule S) (f:Head S→ℝ) (e uJ α θ:ℝ) (H:Cash W s μ L Q o C T R)(j l:ℕ):=(∑ i:Tickets (Palette.sign M' S), packPrice rA i.val * Vbill H (Palette.team M' i) p f j l e uJ α θ)
local notation "g₀" => (promo M' rA p g e uJ α c! H j l)

variable (hx:authorized H p)
include hx
lemma implied : g₀= u₀*(∏ i∈p,crestP M' rA g i)*(1+H.shapeW p)^(l+j) * marking H p * c!^p.card:=by
   unfold promo crestP; simp_rw [Tickets.expanded (Palette.sign M' S) g (Palette.wages M' rA) p]; rw [mul_sum,sum_mul,sum_mul,sum_mul]; refine sum_congr rfl ?_
   intro k _; unfold Vbill; simp only [hx,true_and,Palette.label,Palette.worth]; by_cases he:k.reach⊆p
   · simp only [if_pos he]; unfold Palette.wages; rw [prod_mul_distrib]; unfold packPrice; ring
   rw [if_neg he,if_neg he]; ring
lemma impliesBase : billBase H p g j l e uJ α c! = u₀* (∏ i∈p,g i)* (1+H.shapeW p)^(l+j)*marking H p* c!^p.card:=by
   unfold billBase Vbill; simp [hx, Team.signs,Team.weight, idle]

omit hx
include hG h hw
lemma pricesMarks : 0≤g₀:= sum_nonneg (fun _i _=>mul_nonneg (prod_nonneg fun i _=> hw i) (invoice_base H _ _ hG h))

omit hw
-- montage receipts funded even after position mark-count costs
abbrev VolumeW (B:ℝ)(M j :ℕ):ℝ:=B*2^j*((M+2:ℝ)*2)
def hill (Q:ConnectedActivityE6.Target G P)(L: Side)(μ s:ℝ)(e uJ α θ ρ:ℝ)(j l M:ℕ):= Q.goal L s+VolumeW (speedBill e uJ α j) M j * account Q L μ s (l+j) (creditStencil M θ ρ)
local notation "κ!" => hill Q L μ s e uJ α θ ρ j l M
variable (hq:degreePrice (radiusB s) (goodK.creditStencil M θ ρ*Fort.γprice Q L s μ) Q.δ ≤ 1/2)
    (hp:degreePrice (radiusB s) (hill Q L μ s e uJ α θ ρ j l M) δ ≤1/2)
    (hv:a+δ+δ≤ Q.exp)(he:0<δ)
    {F:Molecule S→ℝ}{gE:Head S→ℝ}(hF : ∀ p,0≤ F p)(hReady:readyBook H gE C' (Fort.γprice Q L s μ))
    (hE : ∀ p,if authorized H p then F p = speedBill e uJ α j*(∏ i∈p,gE i)*(1+H.shapeW p)^(l+j) * marking H p * (goodK.creditStencil M θ ρ)^p.card else F p=0)
    (hg:∀ i,0≤gE i)

abbrev final_bill (f':Molecule S→ℝ)(M :ℕ)(p:H.ThinP) := (M+2:ℝ)*2*f' p.val
set_option quotPrecheck false
local notation "U!" => (final_bill F M (H:=H))

include hq hp hv he hF hReady hE hg
lemma funding : Ready H.smallAt (radiusB s) (fun i=>2^j*U! i) (a+δ) κ! δ (1/2):=by
   have hz:0≤u₀:= by unfold speedBill; have hh:= hG.earn; have hS:=hG.bSc; have hv:=h.effort; positivity
   have hβ: (0:ℝ) ≤(M+2:ℝ):=by positivity
   let t:=(2:ℝ)^j *((M+2:ℝ)*2); have ht:0≤t:=by unfold t; positivity
   let z:=VolumeW u₀ M j
   have hz': z= u₀*t:=by unfold z VolumeW t; ring
   have hJ:= zero_lt_one.trans_le (height H h) -- Maya?
   have hu i:0≤Fort.Pextra H C' i:= by rcases i with i|i; exact mul_nonneg N.conduit.lives.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
   have hK:=paid_mark H gE (Fort.Pextra H C') hg hu (q:=1/2) (u:=c!) (z:=X₂) hReady hJ (fun i=>rfl) hq (l+j)
   have hζ :0 < κ!:= add_pos_of_pos_of_nonneg (Daisy.arable H) (mul_nonneg (show 0 ≤ z by rw [hz']; positivity) (budget_nonneg (hK 0)))
   refine ⟨hζ,he,hp,by norm_num,fun i => mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) zero_le_two) (hF i.val)),fun x=>?_⟩
   have hh:= budget_scale (show 0≤ z by rw [hz']; positivity) (budget_pull (fun i:H.ThinP=>i.val) Subtype.val_injective (hK x))
   refine budget_loosen (budget_mono hh ?_ ?_) (le_add_of_nonneg_left (Daisy.arable H).le)
   · intro i; split; next=> exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hβ zero_le_two) (hF _))) (Real.exp_pos _).le
     rfl
   intro i; split
   next hx=>
      by_cases he':authorized H i.val
      · apply le_trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _))) (mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hβ zero_le_two) (hF _))))
        have h: F i.val=u₀*(∏ t∈ i.val,gE t)*(1+H.shapeW i.val)^(l+j)* marking H i.val* c!^i.val.card:= ((if_pos he').mp (hE i.val)) -- if_pos? imp?
        dsimp only; rw [if_pos (show x∈ H.unionP i.val from hx),if_pos ((H.attends _).2 he'.1)];  rw [h, hz', show H.smallAt i=H.unionP i.val from rfl]; unfold t; apply le_of_eq; ring
      have h0 : F i.val=0:= (if_neg he').mp (hE i.val)
      dsimp only [final_bill]; rw [h0,mul_zero,mul_zero,zero_mul]; exact hh.1 i
   exact hh.1 i

omit hF hReady hg hE
local notation "U₁" => (final_bill (fun p=>billBase H p g j l e uJ α c!) M (H:=H))
lemma axisOne (hR:readyBook H g C' X₂) : Ready H.smallAt (radiusB s) (fun i=> 2^j*U₁ i) (a+δ) κ! δ (1/2):= by
   refine funding hG h hq hp hv he (fun i=> invoice_base H (idle R) i hG h) hR ?_ h.nonneg
   intro i; split; exact impliesBase (by assumption) -- simplif
   next h=> unfold billBase Vbill; rw [if_neg (fun H=> h H.1)]

local notation "U₂" => (final_bill (fun p=> promo M' rA p g e uJ α c! H j l) M (H:=H))
include hw
lemma axisTwo (hR: readyBook H (crestP M' rA g) C' X₂) : Ready H.smallAt (radiusB s) (fun i=> 2^j*U₂ i) (a+δ) κ! δ (1/2):= by
   have hχ i : 0≤ crestP M' rA g i:= nonneg_of_mul_nonneg_left (hR.2.2.2.2.1 i) (Real.exp_pos _)
   refine funding hG h hq hp hv he (fun p=>pricesMarks hG h M' rA hw (p:=p)) hR (fun i=>?_) hχ
   split; exact implied M' rA (by assumption)
   next h=> unfold promo Vbill; simp only [h, false_and, ite_false,mul_zero,sum_const_zero]
end Mill
end Retain
end YM.RGLocalTaylor
