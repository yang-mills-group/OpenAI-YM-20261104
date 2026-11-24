import YM.Pert.Rigid.Camera
import YM.Next.MAXWELL.System
/-!
Horizon-compatible restriction algebra for flag variations in Wick-field coordinates; `Buffer`. Test-adjoining tools will project splitting etc.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.PositionX
open Maxwell Function Labels
open Maxwell.Free Pert.Position Pert Extra.FD
open scoped Topology BigOperators Classical
variable {G : Gauge} (F:Frames G) {d e j : ℕ} (h : d≤e)
abbrev up := (scheme F).rise h
lemma up_same {d} : up F (d:=d) le_rfl = LinearMap.id := LinearMap.ext (fun v=> by apply address_inj F _; exact address_rise F ..)
lemma up_mul (g : e≤j) (v:E F d) : up F g (up F h v)=up F (h.trans g) v := address_inj F _ (by simp only [up,address_rise])
lemma up_inj : Injective (up F h) := by intro x y he; apply address_inj F _; rw [← address_rise F _ h x,← address_rise F _ h y]; exact congr_arg _ he
lemma up_unit : up F h ((Model F).unit d)=(Model F).unit e:= by apply address_inj F _; simp only [up,address_rise,unit_address]
lemma up_conj (v) : (Model F).conj (hierarchy F).spin _ (up F h v)=up F h ((Model F).conj (hierarchy F).spin _ v):= by apply address_inj F _; simp only [up,address_rise,address_star]
lemma up_signed (s : Signed) (v) : rideO F s.ortho e (up F h v)=up F h (rideO F s.ortho d v):= by
  rw [← Pert.Rigid.wear_ride .., ← Pert.Rigid.wear_ride ..]; apply address_inj F _; simp only [up,Pert.Rigid.wear,address_rise,address_motion]
lemma up_pre : lower F d e=LinearMap.range (up F h) := SetLike.ext' (by rw [← stairs_eq F,upward F h (scheme F) (scheme_filters F)])

local notation "L" => up F h
def cut : E F e→ₗ[ℂ] E F d := (_root_.LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.mpr (up_inj F h))).choose
lemma up_cut (v) : cut F h (L v)=v:= DFunLike.congr_fun (LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.mpr (up_inj F h))).choose_spec v
lemma cut_up (v:E F e)(hv:v∈lower F d e) : L (cut F h v)=v:= by rw [up_pre F h] at hv; obtain ⟨q,rfl⟩:=hv; rw [up_cut]
lemma up_stable (B : Buffer F e) (v) : B.val (L v)∈lower F d e:= by
  rcases lt_or_eq_of_le h with he|rfl
  · exact B.property.2.1 d he _ (by rw [up_pre F h]; exact ⟨v,rfl⟩)
  · rw [up_pre F le_rfl,up_same]; exact ⟨_,rfl⟩ -- fill?

def bufferL {e} (B:Buffer F e) : Module.End ℂ (E F e) where
  toFun:=B.val
  map_add':=map_add _
  map_smul':=Rigid.dispatch_cmul F B
lemma bufferL_eq {e} (B:Buffer F e) (p) : bufferL F B p=B.val p:= rfl
def cutL {d e : ℕ} (h : d≤e) (B : Buffer F e) := cut F h ∘ₗ bufferL F B ∘ₗ up F h
lemma cutL_eq (B:Buffer F e) (v:E F d) : L (cutL F h B v)=B.val (L v):= cut_up F h _ (up_stable F h B v)

def zoom (B:Buffer F e) : Buffer F d:=
 ⟨ ((cutL F h B).restrictScalars ℝ).toContinuousLinearMap, by
    let Z:= cutL F h B; have so v:L (Z v)=B.val (L v):=cutL_eq ..
    refine ⟨?_, ?_,fun p=> ?_,fun s p=>?_,map_smul (cutL F h B) _⟩ -- binder p?
    · apply up_inj F h; rw [map_zero]; change L (Z _) = _; rw [so, up_unit,B.property.1]
    · intro j hj p hp; rw [up_pre F hj.le] at hp ⊢; obtain ⟨q,rfl⟩:=hp; let p:=up F hj.le q
      have hh : B.val (L p)∈lower F j e:= B.property.2.1 j (hj.trans_le h) _ (by rw [up_pre F (hj.le.trans h)]; exact ⟨q,(up_mul F hj.le h q).symm⟩)
      rw [up_pre F (hj.le.trans h)] at hh; obtain ⟨r,hr⟩:=hh; refine ⟨r,up_inj F h ?_⟩; change L (up F hj.le r)= L (Z p); rw [so,up_mul F hj.le h r]; exact hr
    · apply up_inj F h; change L ((Model F).conj (hierarchy F).spin _ (Z p))=L (Z _); rw [← up_conj, so,so,← up_conj]; exact B.property.2.2.1 _
    · apply up_inj F h; change L (rideO F s.ortho d (Z p))=L (Z _); rw [← up_signed F h s,so,so,← up_signed F h s]; exact B.property.2.2.2.1 ..⟩
lemma zoom_eq (B) (v:E F d) : L ((zoom F h B).val v) = B.val (L v) := cutL_eq F h B v

def Still (B : Buffer F d) : Prop := ∀ n (p : Fin n → E F d) (x:Points n), x∈conf n → ∑ i:Fin n,visible F d x (Function.update p i (B.val (p i)))=0
lemma visible_eq {n d : ℕ} (p : Fin n→ E F d) (x:Points n) : visible F d x p = Wick.moment G x (address F _ ∘ p) := display F (fun i=>⟨d,p i⟩)
lemma still_pre {B:Buffer F e}(H:Still F B) : Still F (zoom F h B):= by
  intro n p x hx; rw [← H n (L ∘ p) x hx]; apply Finset.sum_congr rfl; intro i hi; rw [visible_eq F, visible_eq F]; congr 1; ext1 j; by_cases hb:j=i
  · subst j; simp only [Function.comp_apply, Function.update_self]; rw [← zoom_eq,up,address_rise]
  · simp only [Function.comp_apply,Function.update_of_ne hb]; rw [up,address_rise]
end YM.PositionX
