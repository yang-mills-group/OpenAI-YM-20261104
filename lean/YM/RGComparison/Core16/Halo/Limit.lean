import YM.RGComparison.Core16.Halo.Beam
/-!
# POS threshold and bulk pin reconstruction

Not convergence from a Poster limit! Step recurrence & shape copies (all-volume, fixed patch clocks G.Offers). Root-fork Γ directed momentum probes charge second moments (using `wt`). Inversion-limit construction separate; here use cover prescription BEAM, aligns with same Lowding for unmasked kin β. Name θ.Pressure.Gr interpreted at `Connector=exp` in Lam. Prop restriction respects all costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Halo
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage Push.Uniform Push.AbsoluteSums.Animals Lam
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{C F c f:Side}{P: Patch}{K:KernelChoices}{d:f.val=c.val*P.L.val}{E:F.val=C.val*P.L.val}{a:ℕ}{W:Oven P}{X:Shelf G (PlaqAxes ⊕ Axis) W.Xways}

-- c numerics, Width sum asymptotic powers to pay at chosen side(c) available after B,L. explicit O(length^{-1}) enough for `due` if using PolePurchase. e tails decrease faster. buyer lemma.
def ready {D:Type}(P:Patch) (X:Shelf G (PlaqAxes ⊕ Axis) D) : ℕ:=100*Pressure.macroR P+24*(X.sector.b+1) -- D
-- monotone in c
lemma stand (h:P.Branches K G) (he:ready P X ≤ c.val): Bid.Larger (G:=G) (StepData.mk P K d):= by
    have hp : c.val≤ f.val:=by rw [d]; exact Nat.le_mul_of_pos_right _ P.L.pos
    exact ⟨h,by unfold ready at he; change 100 * Pressure.macroR P ≤ f.val; omega,by unfold ready at he; omega⟩

def graze (X:Shelf G (PlaqAxes ⊕ Axis) W.Xways) (x t:ℝ) (y:Side):= boundMass x t y X
lemma spell (x v:ℝ)(X:Shelf G (PlaqAxes ⊕ Axis) W.Xways){ι:Type*}{l:Filter ι}{p:ι→Side} (h:Tendsto (fun i=>(p i).val) l atTop): Tendsto (fun i=> boundMass x v (p i) X) l (𝓝 0):= by
    let f i:= (p i).val/16; have he: Tendsto f l atTop:=tendsto_atTop.mpr fun i=> (h.eventually_ge_atTop (i*16)).mono fun j hj=> (Nat.le_div_iff_mul_le (by decide)).mpr hj
    have hp: Tendsto (fun i=> (f i:ℝ)) l atTop:=tendsto_natCast_atTop_atTop.comp he
    have hz (a:ℝ)(ha:0<a) (k:ℕ): Tendsto (fun i=> (f i:ℝ)^k * tail a (f i)) l (𝓝 0):=by
        have htt:=(((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp (hp.const_mul_atTop ha)).div_const (a^k))
        rw [_root_.zero_div] at htt; apply htt.congr
        intro i; unfold tail; dsimp only [Function.comp_apply]; rw [mul_pow,neg_mul]; field_simp
    let a:= Silk.shade X; let F(j:ℕ)(c:ℝ):= fun i=> (f i:ℝ)^j * tail a (f i)*c
    have H(n:ℕ)(c:ℝ): Tendsto (F n c) l (𝓝 0):=zero_mul c ▸ ((hz a shade_pos n).mul_const c)
    have hT : Tendsto (fun i=> tail (rate X) (f i)*(2*x*ceiling 2 (rate X)*countCost (rate X))) l (𝓝 0) := by simpa only [pow_zero,one_mul,zero_mul] using (hz _ (rate_pos X) 0).mul_const (2*x*ceiling 2 (rate X)* countCost (rate X))
    have hP:= (((((H 6 (16*v)).add (H 5 (32*v))).add (H 4 (24*v))).add (H 3 (8*v))).add (H 2 v)).add hT; simp only [add_zero] at hP; apply hP.congr; intro i; unfold F a boundMass ballCost f returnMass; push_cast; ring

-- Proof-independent reset prescription all finite costs after height filtering. Here exact log-Hessian symbol AP.
def small (c:Side) (P:Patch) := c*P.L
def queries (X:Shelf G (PlaqAxes ⊕ Axis) W.Xways)(K:KernelChoices)(w:G.ColorIndex)(k:ℕ)(c:Side) := let d:(small c P).val=c.val* P.L.val := rfl; let S:StepData c (small c P):=⟨P,K,d⟩; let B:= Classical.choice (Tree.select S.ratio P.odd_side); cache (Halo.kernel K W X B w k)

variable (H:P.Branches K G)(h:W.Offers X K) (w:G.ColorIndex) {x y:ℝ}{r k:ℕ}(hX:KernelFare W X K r x)(hy:0≤y)(hY:Reel X y (r+2) (r+2))(hk:k ≤ r)

include h
lemma ensures (d:f.val=c.val*P.L.val)(w:G.ColorIndex)(B:Forest (StepData.mk P K d).ratio)(H: Bid.Larger (G:=G) (StepData.mk P K d))(r:ℕ): cache (kernel K W X B w r) = queries X K w r c:= by
    obtain rfl: f=small c P:= Subtype.ext d
    let Z:=P; let C':=StepData.mk P K d; let Y:=(Classical.choice (Tree.select C'.ratio C'.patch.odd_side))
    apply congr_arg cache (funext fun i=> funext fun j=> ?_); exact congr_arg (nth r) (Lam.convention B h H _ _ Y h) -- basis issue
include H hk hX hy hY
private lemma tipping (C c:Side)(he:ready P X≤c.val)(hc : ready P X≤C.val)(hQ: c.val ∣ C.val) : |queries X K w k C-queries X K w k c| ≤ boundMass x (Lam.Exact K X (r+2) h.good y) c X := by
    let S := StepData.mk P K (show (small c P).val=c.val*P.L.val from rfl); let B:=Classical.choice (Tree.select S.ratio S.patch.odd_side)
    let T := StepData.mk P K (show (small C P).val=C.val*P.L.val from rfl); let Y:=Classical.choice (Tree.select T.ratio T.patch.odd_side)
    obtain ⟨M,hM⟩:=hQ; have hx : 2≤ c.val:=by unfold ready at he; omega
    obtain ⟨Z,hZ⟩:= Silk.fitted (E:=T.sizes) (e:=S.sizes) K hM hx B
    have hr: Bid.Larger (G:=G) S:= stand H he; have hs: Bid.Larger (G:=G) T:= stand H hc
    rw [← ensures h T.sizes w Z hs]; exact bills h hM hx hr hs hZ (by unfold ready at he; omega) w hX hy hY k hk

omit H h hk hX hy hY
def chain (t:ℕ): Side := ⟨t+1,Nat.succ_pos _⟩

def warmer (X:Shelf G (PlaqAxes ⊕ Axis) W.Xways) (K:KernelChoices) (w:G.ColorIndex)(k:ℕ) := limUnder atTop ((queries X K w k) ∘ chain)

local notation "ζ"=> Lam.Exact K X (r+2) h.good y
include H h hk hX hy hY
private lemma rivals (C c:Side)(he:ready P X≤c.val)(hc : ready P X≤C.val):|queries X K w k C-queries X K w k c| ≤ boundMass x (Lam.Exact K X (r+2) h.good y) C X + boundMass x (Lam.Exact K X (r+2) h.good y) c X :=by
    let W:= c*C; have he₁:C.val ≤ W.val:=le_mul_of_one_le_left (Nat.zero_le _) c.pos; have he₂: c.val ≤ W.val:=le_mul_of_one_le_right (Nat.zero_le _) C.pos
    exact (abs_sub_le (queries X K w k C) (queries X K w k W) (queries X K w k c)).trans (add_le_add ((abs_sub_comm ..).trans_le (tipping H h w hX hy hY hk W C hc (he.trans he₂) ⟨_,Nat.mul_comm ..⟩)) (tipping H h w hX hy hY hk W c he (he.trans he₂) ⟨_,rfl⟩))

-- char buyer; applies Bright.Legacy on exact true η.
omit H h hk hX hy hY in
private lemma future : Tendsto (fun i=>(chain i).val) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=>Nat.le_succ i) tendsto_id
lemma issues : Tendsto (fun i:ℕ=> queries X K w k (chain i)) atTop (𝓝 (warmer X K w k)):=by
    let C i:= queries X K w k (chain i); have h₀: ∃ x:ℝ,Tendsto C atTop (𝓝 x) := by
       apply cauchySeq_tendsto_of_complete; rw [Metric.cauchySeq_iff]; intro ε he; let y(p:ℕ):= boundMass x ζ (chain p) X; have ht: ∀ᶠ p in atTop,y p< ε/2:= (spell _ _ _ future).eventually (eventually_lt_nhds (half_pos he))
       obtain ⟨p,hp⟩:=eventually_atTop.1 (ht.and (future.eventually_ge_atTop (ready P X))); refine ⟨p,fun i hi j hj=>?_⟩; rw [Real.dist_eq]; apply lt_of_le_of_lt (rivals H h w hX hy hY hk _ _ (hp _ hj).2 (hp i hi).2); exact (add_lt_add (hp _ hi).1 (hp _ hj).1).trans_eq (add_halves ε)
    exact tendsto_nhds_limUnder h₀
lemma owes (c:Side)(hu:ready P X≤c.val): |queries X K w k c -warmer X K w k| ≤ boundMass x ζ c X:= by
    let Y:= issues H h w hX hy hY hk |>.const_sub (queries X K w k c)|>.abs
    let v(p:Side) := boundMass x ζ p X; have hx:= (spell x (Lam.Exact K X (r+2) h.good y) X future).const_add (v c); rw [add_zero] at hx; exact le_of_tendsto_of_tendsto Y hx ((future.eventually_ge_atTop (ready P X)).mono fun i hi=>rivals H h w hX hy hY hk _ _ hi hu)
end YM.RGComparison.Core16.Halo
