import YM.MS.Garment.Apatite
import YM.MS.Garment.Humor
import YM.MS.Color.Group
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Coh
/-!
# Compact color rotation after lifting

All finite-D values; fixes external tensors unlike permutation sign. Quaternion anti via
 BV differential. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric Color
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{b c: Bool}{m n:ℕ}{U:Rip G}{F H:Mob G}
variable {D P: Type}[Fintype D] [DecidableEq D] [AddCommGroup P]

def ShadeG (F:Mob G) : Prop:= ∀ m (g:G.El), repeatC g (F m)=F m
def ReadyG (U:Rip G): Prop:=∀ m (g:G.El), Transport (dye g) (U m) (U m)
variable (hf:ShadeG F)(hr:ReadyG U)(g:G.El)
lemma pull_color (h:m≤n) (F:Rack G n): repeatC g (pulls h F)=pulls h (repeatC g F):= by
    funext l; induction l generalizing F with| nil=> simp [pulls,Arts.lift]| cons i l ih=> rcases i with ⟨⟨a,b⟩,p⟩; unfold pulls at *; rw [repeat_cons,show Arts.lift h (((a,b),p)::l)=(embA _ (a,b),Left h p)::Arts.lift h l from rfl, repeat_cons]; apply Finset.sum_congr rfl; intro j _; exact congr_arg (wc g b j * · ) (ih (D (((Option.map (rises h) a.1, a.2), j), Left h p) F)) -- placeholder a.extend
include hf hr
lemma apex_pig (hh:Form0 b F)(hp: Knot b U) (i:ℂ)(m:ℕ)(q:SectorP m): repeatC g (Wtr i U F q)=Wtr i U F q:= by
    have hm (n:ℕ) (h:m≤n): repeatC g (Wtr n U F q)= Wtr n U F q := by
        have hv: Wtr n U F q = pulls h (trc (U n) (Left h q) (F n)):= funext fun l=> tallyN hh.token hp.token h;
        obtain he: beam (dye g) (trc (U n) (Left h q) (F n))=trc (U n) (Left h q) ((dye g).beam (F n)):= (hr n g).shuttle0 (Left h q) (F n); rw [brush g,hf n g] at he; rw [hv,pull_color,he] -- maybe duplicate
    rw [combo i m,map_add,map_smul,map_sub,hm m m.le_refl,hm (m+1) (by omega)] -- rhs combo expanded?
lemma scenery (H:Form0 b F)(hp:Knot b U){i:ℂ}(hi:i∈Town): ShadeG (ocean i U F):= by
    intro m g; rw [← brush]; let W:= dye (D:=Arts.L m) (P:=SectorP m) g; funext l; apply sub_eq_zero.mp
    apply Garment.erase hp H hi (L:=fun F:Rack G m=> beam W F l- F l) ( (Centre _).sub_mem (W.sense|>.reaches l) (centroid _)); intro x; rw [show beam W= repeatC g from brush g,pull_color,apex_pig]; exacts [sub_self _,hf,hr,H,hp]
lemma tree_hues (ht: ShadeG H)(hx:closedF U b): ShadeG (arbor U F H):= by
    intro n i; unfold arbor; rw [← brush,(hr n i).gatherR _ _ (hx n) (hx n),brush i,hf n i,ht n i]
omit hr in lemma hue_scale (s:ℝ)(a:ℂ): ShadeG (plow a s F):= by
   intro i g; have he (f:Rack G i) (l): repeatC g (fun q=> amount (a+ mass q) s* f (sr s q)) l= amount (a+ ↑(mass l)) s* repeatC g f (sr s l) := by
       induction l generalizing a f with
       | nil=> simp [sr]
       | cons y l ih=>
         rcases y with ⟨⟨r,p⟩,q⟩; rw [repeat_cons,show sr s (((r,p),q)::l) = ((r,p),exp s • q)::sr s l from rfl,repeat_cons,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [show D (setLeg ((r,p),q) j) (fun v:Legs (Shore G i)=>amount (a+mass v) s*f (sr s v))=(fun v:Legs (Shore G i)=> amount (a+ wfield (r,p)+mass v) s* D (setLeg ((r,p),exp s • q) j) f (sr s v)) from funext (fun v=> by simp only [at_D,Price_cons,sr,List.map_cons,Int.cast_add, add_assoc]), ih]; simp only [Price_cons, Int.cast_add, ← add_assoc]; rw [mul_left_comm]

   funext l; unfold plow; rw [he,hf i g] -- nested
end YM.MS.Garment
