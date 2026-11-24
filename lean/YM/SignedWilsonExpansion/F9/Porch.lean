import YM.SignedWilsonExpansion.F9.Bowler
import YM.Next.WARD_BIN.Wheels
import YM.Next.WARD_BIN.Hats
/-! # Pay the aperture at the inversion addresses

Finite widths for each pose, so no top pole on query winding. This is an
auxiliary regulator identity before taking ANY of the physical limits. In
particular it holds with translations but within the phase-safe sector; use
`Terms.drop` with the indicated finite cone proofs.
-/
set_option autoImplicit false
set_option maxHeartbeats 620000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa.StationA
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Cloth XSpace
open PertExtension PertExtension.Orb FormalOPE FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal InnerProductSpace
variable {G:Gauge}{H:Hol G}{h i j k a m r d n l:ℕ}{F:Frame G h}{x:Label G h}{P:Period} {s:Side} {ι:Type*}

-- Local metric reporting radius in lattice units. intentional 8 slack at occurrences of true data, but can purchase at precise width too.
def away (x: Site s)(a:ℕ):Finset (Site s):= Finset.univ.filter (fun q=> a<separation q x ∧ a<separation q (-x))
lemma away_misses {x q: Site s}: q∈away x a ↔ a<separation q x ∧ a<separation q (-x):= by simp [away]
lemma away_tiny {x:Site s}(q:a≤m): away x m⊆ away x a:=fun i h=> away_misses.mpr ⟨q.trans_lt ((away_misses.mp h).1),q.trans_lt ((away_misses.mp h).2)⟩
lemma mirror_neg (x y:Site s): separation (-x) (-y)=separation x y:=by rw [separation,show -x- -y= -(x-y) by abel,pdist_neg]; rfl
lemma draws {t:Signed}{x:Site s}(a:ℕ): (away x a).image (affine t 0)⊆ away (t.act x) a:=by intro b hb; obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hb; apply away_misses.mpr; obtain ⟨hQ,hE⟩:= away_misses.mp hp; unfold affine; rw [add_zero,separation_signed, ←Signed.act_neg,separation_signed]; exact ⟨hQ,hE⟩
lemma vision (S: Finset Cover)(x y:Site s) (C:ℕ)(p:C+cord S<separation y x)(q:C+cord S<separation y (-x)):
    footprint S y⊆away x C := by
    intro i h; obtain ⟨j,hj,hv⟩:= halo_spec.mp (contained S y h); obtain rfl:= Finset.mem_singleton.mp hj; apply away_misses.mpr; have ht := separation_triangle j i x; have he := separation_triangle j i (-x); omega
section
variable (x:Site s){S:Finset Cover}(p:Rays G h H)(f:p.FitsAt S) {v:Config G s→ℝ}
include f
private lemma first_pos (a:p.edg): separation x (edgeAt a.val x).1≤cord S:= by
    obtain ⟨b,H,B⟩:= halo_spec.mp (contained S x (Finset.mem_image.mpr ⟨a.val.1,(p.fitsAt_edge f a).1,rfl⟩)); obtain rfl:= Finset.mem_singleton.mp H; exact B
-- take *second* endpoint of mirror (equals -(first of bond))
private lemma mirror_end (a:p.edg): let b:= Orb.reflect (edgeAt a.val x); b.1+ Lattice.step b.2= -(edgeAt a.val x).1:=by intro b; unfold b Orb.reflect; dsimp only; exact sub_add_cancel ..
lemma mirrorSafe (u: 2*cord S < separation x (-x)) (a:p.edg): avoids (edgeAt a.val x) (footprint S x):=by
   right; intro at_; rw [mirror_end x p f a] at at_
   obtain ⟨b,hb,B⟩:=halo_spec.mp (contained S x at_); rw [Finset.mem_singleton.mp hb] at B; have ht:= first_pos x p f a; have hsum:= separation_triangle x (-(edgeAt a.val x).1) (-x); rw [mirror_neg,separation_comm (edgeAt a.val x).1] at hsum; omega
lemma is_far (p':cord S≤k)(a:p.edg): off (edgeAt a.val x) ↑(away x k) := by
   have h:= (first_pos x p f a).trans p'; constructor
   · left; exact fun ht=> (away_misses.mp ht).1.not_ge ((separation_comm ..).trans_le h)
   right; rw [mirror_end x p f a]; exact fun ht=> (away_misses.mp ht).2.not_ge ((mirror_neg ..).trans_le ((separation_comm ..).trans_le h))
end
-- cash rotation for arbitrary posed spectators
lemma proxyTurn {f:Config G s→ℝ}(p:Proxy f)(x:Signed):Proxy (f ∘ pull x 0) := by
    obtain ⟨F,h,rfl⟩:=p
    let a(e: Edge (Site s)):= (posDir e.2).rotate x; let b(e:Edge (Site s)):= affine x 0 e.1; let c: ArrayOf G s→ArrayOf G s:= fun U e=> if (a e).neg then star (U ((a e).used (b e))) else U ((a e).used (b e)); have hc:ContDiff ℝ ∞ c:=by apply contDiff_pi.mpr; intro i; unfold c; split; exact (starL' ℝ).contDiff.comp (contDiff_apply ..); exact contDiff_apply ..
    refine ⟨F∘ c,h.comp hc,?_⟩; funext U; apply congr_arg F; funext i; unfold image pull; unfold Lattice.Step.read; unfold c a b; split <;> rfl

-- move a centered rotated column back to original stencil on same box
lemma placement_turn (x:Site s)(f:Pill G)(k:Signed): places x (Pill.spins f k).f= places (k⁻¹.act x) f.f ∘ pull k 0:=by
    funext U; unfold places Pill.spins; simp only [Function.comp_apply]; rw [expandAt_pull]; simp only [affine,Signed.act_inv, add_zero]
-- No group invariance of spectators needed except `PreTest` for conversion.
theorem measureTurn {Q:Config G s→ℝ} (g:Even s.val) {S:Finset Cover}(R:Rays G h H)(p:R.FitsAt S)(M:Tensor.T (Snap G h) ℂ (r+1))(h:Rays.covariantTensor M)(x:Site s)(k':ℕ)(v:FitsIn S s)
    (hb:k'≥cord S) (hv: 2*cord S < separation x (-x)) (s':Signed)(hZ:LocalOn ↑(away x k') Q) (hp:Proxy Q): 
    ∀ t,t ≠ 0 → preExpectation (places x ((Pill.holder R M h).spins s').f*Q) t=t^2*preExpectation (places x ((Pill.sink R M h).spins s').f*Q) t:=by
    set u:=s'⁻¹.act x; set Q' := Q ∘ pull s'⁻¹ 0; have hg:Proxy Q':= proxyTurn hp _
    have hw (P:Pill G): places x (P.spins s').f * Q= (places u P.f * Q') ∘ pull s' 0:=by rw [placement_turn]; funext y; unfold Q' u; simp only [Pi.mul_apply,Function.comp_apply,pull_pull,mul_inv_cancel,affine, Signed.act_zero, add_zero,pull_id];
    have hx: 2*cord S<separation u (-u):=by unfold u; rw [← Signed.act_neg,separation_signed]; exact hv
    have hR : LocalOn ↑(away u k') Q':=by
        refine fun X Y h=> Wheels.trans_local s'⁻¹ 0 hZ _ _ (agrees_mono h ?_); exact draws _
    intro t ht; simp_rw [hw, InversionWard.beforeTurn g s' (neg_zero ..) ((proxy u (Pill.holder R M h).valid).cont.mul hg.cont), InversionWard.beforeTurn g s' (neg_zero ..) ((proxy u (Pill.sink R M h).valid).cont.mul hg.cont)]
    exact measureWard R M p h u hg hR v (mirrorSafe u R p hx) (is_far u R p hb) g t ht
end YM.WilsonCoeffUV.Mer.Xa.StationA
