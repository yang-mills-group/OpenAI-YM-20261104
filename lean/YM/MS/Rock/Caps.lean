import YangMills.WilsonProof.NativeSupport.YM.MS.Rock.Stone
/-!
# Compact geometry stencil (internal)

Supports: prescribe by sup absolute momentum at fixed dimension, but approxim
 isotropic. Integrating Wtr_z partly extra dimension still compact-uniform. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock.Path
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E F H J:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {m n k:ℕ}{z:UScale I}{a b : I→ℝ}{r:ℝ}{f:I→ Mob G}{u:I→ Rip G}
-- allocate cut radius sup independent of m; later approximation theorem actual `Rad` supports.
def rock (A:ℝ)(K: Rip G): Prop:=∀ m i j p, A<‖p‖→ K m i j p=0
lemma bigKey (p:SectorP m)(t:ℝ): t≤‖slideA (Nat.lt_succ_self m) (p,t)‖ := by
   obtain hp:=equal0 (p,t) (Nat.lt_succ_self m); obtain hs:= congr_arg Prod.snd hp; let A:=hatch (Nat.lt_succ_self m); let x:= slideA (Nat.lt_succ_self m) (p,t); have hh:x A=t:=hs; exact (le_abs_self t).trans ((congr_arg norm hh).symm.le.trans (norm_le_pi_norm ..)) -- abs vs norm_eq
lemma ledge (h:m≤n)(p:SectorP m): ‖p‖ ≤ ‖Left h p‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> (congr_arg norm (lasts (rises h) p i)).symm.le.trans (norm_le_pi_norm ..)
variable {U:Rip G} {F:Mob G} {B:ℝ} {s:ℂ}
lemma heroZ (h:rock B U)(F:Mob G)(z:ℂ){p:SectorP m}(i:Legs (Shore G m))(hp:B<‖p‖): Wtr z U F p i=0:= by
    unfold Wtr; simp only [Pi.smul_apply,Pi.add_apply, at_trc,yeast,token,fleck]; simp_rw [h m _ _ p hp, h _ _ _ _ (lt_of_lt_of_le hp (ledge (Nat.le_succ m) p)),zero_mul, Finset.sum_const_zero,smul_zero, add_zero]
lemma planeW (h:rock B U)(F:Mob G)(w:Touch G m E) (z:ℂ): towards B (wing z U F w) :=fun p t _ ht=> heroZ h F z _ (ht.trans_le (bigKey p t))
lemma wing_ref {X:Spin (L (m+1))}{u v:SectorP (m+1)}{b:Bool}(H: Sturdy b F)(hv: Ruddy b U)(s:ℂ)(h: X.turn u=v)(l:Legs (Shore G m))(ht: ∀ q:SectorP m,X.turn (Left (Nat.le_succ m) q)=Left (Nat.le_succ m) q): Wtr s U F v (Arts.lift (Nat.le_succ m) l)= Wtr s U F u (Arts.lift (Nat.le_succ m) l):= by
    obtain he:= congr_fun (twirls H hv X (fixedLeft _ ht) s (x:=u)) (Arts.lift (Nat.le_succ m) l); rw [beam_only (Nat.le_succ m) X ht _ l, h] at he; exact he
lemma wing_mirror {b:Bool}(H:Sturdy b F)(hv:Ruddy b U)(s:ℂ)(W:Touch G m E): mirror (wing s U F W):=by
    intro p t x; let u:=Nat.lt_succ_self m; let X:=Spin.spark (hatch u); have hx : ∀ i:SectorP m, X.turn (Left u.le i)=Left u.le i:= lightOn u.le (step u);
    exact wing_ref (X:=X) H hv s (show X.turn (slideA u (p,t))= slideA u (p,-t) from by rw [Path.path,Path.path,map_add,map_smul,hx, show X.turn _ = _ from sees_p (hatch u)]; simp) _ hx
variable {Z:I→ℂ}{σ:Bool}
-- estimates primitive
lemma compact_fin (h:∀ n:ℕ,scaleC z 1 fun i=> ‖(2*(Z i-n):ℂ)‖)(hf:fell z a f)(hv:rib z b u)(hp:∀ i, ups (Z i))(hB:1≤B)(hw:∀ i,rock B (u i))(H:∀ i, Sturdy σ (f i))(hr:∀ i,Ruddy σ (u i))(hb:∀ i,0≤b i):
    fell z (fun i=>b i*a i * LogMass B (Z i)) (fun i=>ocean (Z i) (u i) (f i)):= by
    intro m E _ _ _ w; simp_rw [oceanic h hf hv hb]; exact Arc.compact_sky _ (sky h hf hv hb w) (fun i=>wing_mirror (H i) (hr i) (Z i) w) (fun i=>planeW (hw i) (f i) w _) hB hp m -- application ... ellipses
lemma regular_fin (h:∀ n:ℕ,scaleC z 1 fun i=> ‖(2*(Z i-n):ℂ)‖)(hf:fell z a f)(hv:rib z b u)(hp:∀ i,ups (Z i))(ht:∀ i,2*(Z i).re+1≤(n:ℝ))(H:∀ i,Sturdy σ (f i))(hr:∀ i,Ruddy σ (u i))(hb:∀ i,0≤b i) : fell z (fun i=>b i*a i) (fun i=> ocean (Z i) (u i) (f i)):= by
    intro m E _ _ _ w; simp_rw [oceanic h hf hv hb]; exact Arc.swoop_bill _ (sky h hf hv hb w) (fun i=>wing_mirror (H i) (hr i) (Z i) w) m hp ht
end YM.MS.Rock.Path
