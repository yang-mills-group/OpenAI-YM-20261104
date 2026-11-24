import YM.FVA2.O.Product.Nectars
/-!
# Leibniz including tree as second derivation with odd line
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Serve
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff
open scoped Topology ContDiff
variable {G:Gauge}{x y z:Law G}{t:Bool}{a b:QP}{U:Edge G}{I E:Type}{u:ℝ}
local notation "Ψ"=> Lifting.sense G
local infix:70 " ⋄ " => product (field Landau.parity)
lemma gust (p:QP)(h: closed U Landau.parity t)(hx:Pure (field Landau.parity) false x)(hy:Pure (field Landau.parity) false y): link (trc U p) t ( field Landau.parity ) x (y ⋄ z)= link (trc U p) t (field Landau.parity) x y ⋄ z + y ⋄ link (trc U p) t ( field Landau.parity ) x z := by
    unfold trc; simp_rw [ link_sum, link_scale,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; by_cases ht: U i j p=0; simp [ht]; rw [ pair_products (p:=field Landau.parity) (i,p) (j,-p) ( h i j p ht ) hx hy, smul_add ]
lemma pack (h:closed U Landau.parity t)(hx: Pure (field Landau.parity) false x )(hy: Pure (field Landau.parity) false y) (S:Finset QP) : link (slab U S) t (field Landau.parity) x (y ⋄ z)= link (slab U S) t (field Landau.parity) x y ⋄ z + y ⋄ link (slab U S) t (field Landau.parity) x z:= by unfold slab; simp_rw [ link_sum,map_sum,LinearMap.sum_apply, gust _ h hx hy, Finset.sum_add_distrib ]
lemma ride {x:I→E→ℂ}{f:E→ ℂ}{l: Filter I}{L:(E→ℂ)→ℂ}(h:∀ i,∀ᶠ k in l, x k i=f i)(hv:L∈ Heat.Centre E): ∀ᶠ k in l,L (x k)=L f:= by
    refine Submodule.span_induction (p:=fun L _=> ∀ᶠ k in l,L (x k)=L f) ?_ (Eventually.of_forall fun _=>rfl) (fun x y _ _ hx he=> ?_) (fun t i _ hi=> hi.mono fun k hk=> congr_arg (fun v:ℂ=> t • v) hk ) hv -- subgoal order
    · rintro j ⟨i,rfl⟩; exact h _
    exact (hx.and he).mono fun k hk=> congr_arg₂ (·+·) hk.1 hk.2
lemma tree_derive (h:closed U Landau.parity t)(hx: Pure (field Landau.parity) false x )(hy: Pure (field Landau.parity) false y) : boulevard Landau.parity U x (y ⋄ z)= boulevard Landau.parity U x y ⋄ z + y ⋄ boulevard Landau.parity U x z := by
    simp_rw [blvd]
    funext l; simp only [ ← tree_trans ( F:=x ),Pi.add_apply ]; let X:= translate x; obtain ⟨k,hk,hy',hz'⟩:= (( roll_tree Landau.parity X (y ⋄ z) U l ).and (( ride (roll_tree Landau.parity X y U) (( buyer z ).reaches l) ).and ( ride (roll_tree Landau.parity X z U) ((seller y).reaches l) ))).exists;
    rw [← hk, ← hy', ← hz']; dsimp only [X]; simp_rw [stickT h k (trans_off x)]; exact congr_fun (pack (cl_trim k h) (pure_trans hx) hy k) l
lemma cr_derive (h:Rolled U)(hh:closed U Landau.parity t)(hP:x∈Roof G)(hc:y∈Roof G)(hF:z∈ Wallet G) : crossF U t x (y ⋄ z)= crossF U t x y ⋄ z + y ⋄ crossF U t x z := by
    have hx:Pure (field Landau.parity) false x:= hP.2; have he w:= supplier (t:=t) h hP.1 ( show y∈ Wallet G from hc.1 ) hx w; have hv w:= supplier (t:=t) h hP.1 hF hx w; funext l; obtain ⟨hA,hB⟩:= cent_arguments planeF ( ( buyer z ).reaches l ) (fun i=>(he i).1); obtain ⟨hC,hD⟩:= cent_arguments planeF ((seller y).reaches l) (fun i=>(hv i).1); rw [ (supplier h hP.1 ( Wallet.product hc.1 hF ) hx l).2 ]; simp_rw [gust _ hh hx ( show Pure (field Landau.parity) false y from hc.2 ),Pi.add_apply]; rw [ integral_add hA hC,funext (fun i=>(he i).2), funext (fun i=>(hv i).2) ]; exact congr_arg₂ (·+·) hB hD
lemma gira (hP:x∈Roof G) : (Φ G u).J (x ⋄ y)= (Φ G u).J x ⋄ y+ x ⋄ (Φ G u).J y+ crossF (lineB G u) true x y:= by
    let L:=Heat.orbit (lineB G u) planeF; let X:=(Wick.Q G 0).move; have hp : Pure Ψ false x := hP.2; change ((X.Q+L) (x ⋄ y))= ( X.Q x + L x ) ⋄ y + x ⋄ ( X.Q y+ L y ) + link L true (field Landau.parity) x y; rw [LinearMap.add_apply,X.product_rule, hp.signs,cross_false',one_smul,link_even L (b:=true) hp,map_add, map_add,LinearMap.add_apply]; abel
lemma pira (hP:x∈Roof G) : (Φ G u).P (x ⋄ y)=(Φ G u).P x ⋄ y + x ⋄ (Φ G u).P y+ crossF (lineA G u) false x y := by
    change (Φ G u).P (x ⋄ y)= _+ link (Φ G u).P _ (Lifting.sense G) _ _; rw [link_even (p:=Lifting.sense G) (Φ G u).P (b:=false) (show Pure Ψ false x from hP.2) ]; abel -- binder
end YM.FVA2.O.Serve
