import YM.MS.Rock.Wing
import YM.MS.Rock.Sum
/-!
# Claims for dimensional rod integrands

Price uniform per b in rapid. Wtr definition at arbitrary embedding (provided C∘L A=id). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {G:Gauge}{I E F H J A:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup H][NormedSpace ℝ H]{m n:ℕ}{Z:I→ℂ}
variable {z:UScale I} {a b d:I→ℝ}{u:I→ Rip G}{g:I→ Mob G}
variable [FiniteDimensional ℝ E][FiniteDimensional ℝ F] {W:Touch G m E}
    (A:F→L[ℝ] SectorP m)(C:SectorP m→L[ℝ] F) (h:∀ i,C (A i)=i) 
    (hg: fell z a g)(hr:rib z b u)(hb:∀ i,0≤b i)
def move (w:m≤n)(W:Touch G m E): Touch G n E:= W.map (fun i=> (embA (rises w) i.1, (Left w) ∘L i.2))
omit [FiniteDimensional ℝ E] in
lemma moves (w:m≤n)(W:Touch G m E)(x:E): Arts.lift w (sail W x)= sail (move w W) x:= by simp only [sail,Arts.lift,move,List.map_map]; rfl
include h hg hr
lemma element (c d:Cfield G m)(W:Touch G m E): quiet z (fun i (p:F×E)=> u i m c d (A p.1)* g i m ((c,A p.1)::(d,-A p.1)::sail W p.2)) (fun i=> b i* a i):= by
   let V : F× E→L[ℝ] SectorP m:= A ∘L ContinuousLinearMap.fst ℝ F E; let L:= Wire.lift W ( ContinuousLinearMap.snd ℝ F E); have he:= (Line.rapid (F:=E) (ride_peak (hr m c d) h)); convert! he.mul (hg m (F×E) ((c,V)::(d,-V)::L)) using 1; simp_rw [fieldVal,sail_cons,L,lift_sail]; rfl
include hb
lemma sections (W:Touch G m E): quiet z (fun i (p:F×E)=> trc (u i m) (A p.1) (g i m) (sail W p.2)) (fun i=>b i*a i):= by
    simp_rw [at_trc]; exact tranquil _ (fun c _=>tranquil _ (fun d _=> element A C h hg hr c d W) (fun i=>mul_nonneg (hb i) (znon hg i))) fun i=> mul_nonneg (hb i) (znon hg i)
variable (hm: scaleC z 1 fun i=>‖(2*(Z i-m):ℂ)‖)
include hm
lemma higher (W:Touch G m E): quiet z (fun i (p:F×E)=> Wtr (Z i) (u i) (g i) (A p.1) (sail W p.2)) (fun i=> b i*a i):= by
   let r:= Nat.le_succ m; let V:= Left r ∘L A; let X:= C ∘L Cl r; have hx p : X (V p)=p:= by change C (Cl _ ((Left _) (A p)))= p; rw [leftCl,h]
   let aH i:=b i*a i; have hp (i:I):0≤aH i:= mul_nonneg (hb i) (znon hg i); let i:= step (Nat.lt_succ_self m); let l c s:= (vleg s (aside r i) c:Cfield G _)
   simp only [Wtr,Pi.add_apply,Pi.smul_apply,smul_eq_mul]; apply Rapid.add (sections A C h hg hr hb W); have he: quiet z (fun i (p:F×E)=> yeast (u i) (g i) (A p.1) (sail W p.2)) aH:= by
       unfold yeast; refine tranquil _ (fun s _=> tranquil _ (fun c _=>tranquil _ (fun t _=>tranquil _ (fun d _=> ?_) hp) hp) hp ) hp
       convert! element V X hx hg hr (l c s) (l d t) (move r W) using 1; simp_rw [token,fleck, moves]; rfl
   simpa only [Pi.one_apply,mul_one] using Cquiet he hm
-- moment Tok projection to m+1 radical eval
end YM.MS.Rock
