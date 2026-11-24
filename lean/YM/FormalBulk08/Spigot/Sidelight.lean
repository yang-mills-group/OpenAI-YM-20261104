import YM.FormalBulk08.Spigot.Stack
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius

-- choose O(|v|) canonical walks including differing deterministic stencils
structure Herald where
    path : Face ℤ→Slot
    shape:∀ p,(path p).offset=p.1∧ (path p).plaq=p.2
    C : ℝ
    active : 0<C
    price : ∀ p,((path p).length:ℝ) ≤ C*(1+size p.1)

def herald : Herald:= ⟨fun p=>walkSlot p.2 p.1,fun p=>⟨walkSlot_end ..,rfl⟩,4,by norm_num,fun p=>by rw [walkSlot_cost]; push_cast; linarith⟩
structure Dill where
    sap : Pillow→ Cover→ℝ
    n : Stoop→ℕ
    fans : ∀ x,Fin (n x)→Plaque
    pos : ∀ x,Bars (size x.1) (fans x)
    cap : ∀ p,n p≤4*size p.1
    measure : ∀ v:Pillow, ∀ A:ℝ, (∀ x, |v x| ≤ A)→ ∀ x:Cover,|sap v x|≤4*size x*A
    notes : ∀ U:Pillow,∀ x:Stoop, glint (sap U) U x.1 (axisEquiv.symm x.2) = ∑ i:Fin (n x),dropP (fans x i) U
lemma dill : Nonempty Dill:= by
    obtain ⟨G,h,hp⟩:= pool Finset.univ; choose n f he hh ht using fun p:Stoop=>hp p.1 _ (Finset.mem_univ (axisEquiv.symm p.2)); refine ⟨⟨G,n,f,hh,fun x=> ?_,fun x=>?_,fun u x=>ht x u⟩⟩
    · simpa [Axis] using he x
    have he:=h x; simpa [Axis] using he
namespace Dill
variable (D:Dill)
abbrev Hats (w:chain Stoop r):= (i: Fin r)→Fin (D.n (w i))
local notation "N" => chain Stoop
abbrev Compass (r:ℕ):= Σ w:chain Stoop r,D.Hats w
def fable (p:Compass D r)(i:Fin r):=D.fans (p.1 i) (p.2 i)
def windP (U:Link G n)(x: Cover)(i:hue G):= D.sap (stroke U i) x
def aer (U:Link G n):= U ∘ Lotus.drip n + loped (windP D U)
lemma wind_pay (U:Link G n): Stipend (prairie (D.windP U)):= by
    refine ⟨4*‖U‖,1,mul_nonneg (by norm_num) (norm_nonneg _),fun p=> ?_⟩
    rw [Real.norm_eq_abs]; apply (D.measure (stroke U p.2.2) ‖U‖ (fun x=> by rw [←Real.norm_eq_abs]; exact norm_le_pi_norm U (wrap n x.1,coord x.2,p.2.2)) p.1).trans
    rw [liftCost,pow_one]; nlinarith [norm_nonneg U]
lemma aer_pay (U:Link G n): Stipend (D.aer U):= subsidize (stipend_level U) (ranch _ (D.wind_pay U)).2.1 true
lemma sky (U:Link G n)(w:Stoop)(a:hue G): D.aer U (w.1,w.2,a) =∑ i,dropP (D.fans w i) (stroke U a) := by
    refine Eq.trans ?_ (D.notes (stroke U a) w)
    unfold aer glint loped prairie precipice windP; rw [Pi.add_apply, Pi.sub_apply]; unfold stroke; rw [show coord (axisEquiv.symm w.2)=w.2 from axisEquiv.apply_symm_apply _]; rw [←add_sub_assoc]; rfl
variable (R: Herald)
def oracle (p:Compass D r)(T:Tile (edgeL G) r): Atom G r where
    leg i:=R.path (D.fable p i).2
    coeff x:= T (arctic G r (p.1,x))*∏ i,(D.fable p i).1
lemma oracle_invar (p:Compass D r)(T:Tile (edgeL G) r)(ht:Lust T): (oracle D R p T).Invariant := fun u x=> by
    unfold Atom.poly oracle; simp only; simp_rw [mul_right_comm _ (∏ i, (D.fable p i).1),←Finset.sum_mul]; rw [pigment T ht]
lemma sky_cost (p:Compass D r)(T:Tile (edgeL G) r): (oracle D R p T).magnitude=∑ x,|T (arctic G r (p.1,x))|:= by
    unfold Atom.magnitude oracle; simp_rw [abs_mul,Finset.abs_prod,show ∀ i:Fin r,|(D.fable p i).1|=1 from fun i=> (D.pos (p.1 i) _).1,Finset.prod_const_one,mul_one]
lemma deline (o:Loc G 1)(p:Compass D r)(T:Tile (edgeL G) r)(x): (((oracle D R p T).length):ℝ) ≤ r * R.C *(1+ herb (fame _) (0,o) (arctic G r (p.1,x))):= by
    let m:= herb (fame _) (0,o) (arctic G r (p.1,x)); unfold Atom.length oracle; rw [Nat.cast_sum]; apply le_trans (Finset.sum_le_sum (g:=fun _ : Fin r=>R.C*(1+m)) (fun i _=>?_)) _
    · rw [mul_assoc,Finset.sum_const]; simp [m]
    refine (R.price _).trans (mul_le_mul_of_nonneg_left ?_ R.active.le); gcongr; exact ((D.pos _ _).2.trans (show size (p.1 i).1 ≤ m from seat_ink o (arctic G r (p.1,x)) i))
lemma inspection (p: Compass D r)(T:Tile (edgeL G) r)(U:Link G n): traceP U (PowerSeries.coeff r (paste (spring (D.oracle R p T))))=
   ∑ v:chain (hue G) r,T (arctic G r (p.1,v))*∏ i,dropP (D.fable p i) (stroke U (v i)):= by
   rw [springPin]; unfold Atom.poly oracle; dsimp only; refine Finset.sum_congr rfl fun v _=>?_ ;rw [mul_assoc,←Finset.prod_mul_distrib]; congr 1; refine Finset.prod_congr rfl fun i _=>?_ ; let a:Face ℤ:= (D.fable p i).2; rw [show slotFace _ _=(wrap n a.1,a.2) by unfold slotFace; rw [(R.shape _).1,add_zero,(R.shape _).2],strokePin];rfl
lemma display (U:Link G n)(T:Tile (edgeL G) r){o:Loc G 1}(hs:0<σ)(h:Knoxville (fame _) σ (0,o) T A)(he:Torrid T σ 0 o)(hv:Agate T): Broc.blur (sieve n T) U=∑' w:chain Stoop r,∑ v:D.Hats w, traceP U (PowerSeries.coeff r (paste (spring (D.oracle R ⟨w,v⟩ T)))) := by
   rw [blur_tariff U T h hs,←tariff_grain T hv h hs he _ (fun _=>D.aer U) (fun _=>stipend_level U) (fun _=>D.windP U) (fun _=>D.wind_pay U) (fun _=>rfl)]
   let f(v :chain (edgeL G) r):= T v*∏ i, D.aer U (v i); have hf: Summable f:= ((pays_product (r:=r) (fun _=>D.aer U) o hs (fun _=>D.aer_pay U)).choose_spec.2 T A h).1
   let e:=arctic G r; change (∑' v,f v)=_; rw [←Equiv.tsum_eq e f];change (∑' v,(f ∘ e) v)=_; rw [(e.summable_iff.mpr hf).tsum_prod]; apply tsum_congr; intro w; rw [tsum_fintype]; simp_rw [inspection]; rw [Finset.sum_comm (s:=(Finset.univ:Finset (D.Hats w)))]; refine Finset.sum_congr rfl fun x _=>?_; change T _ * (∏ i, D.aer U ((w i).1,(w i).2,x i)) =_; simp_rw [sky,Fintype.prod_sum]; exact Finset.mul_sum ..
end Dill
end YM.FormalBulk08.Spigot
