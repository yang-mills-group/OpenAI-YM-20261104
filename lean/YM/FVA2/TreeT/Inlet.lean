import YM.FVA2.TreeT.Graft
/-!
# Highest-rank projection term for the pole program

Combining tree terms; use in the `Archive` calculation.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Landau MS.Arts MS.Arc MS.Plane.Wire MS.Rock MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Alps MS.Garment MS.Color
open _root_.YM.MS.Shine MS.Hem MS.Hem.Mell MS.Train MS.Pearl MS.Motif MS.Heat.Signal MS.Book MS.Book.Convolve MS.Garment.Wave MS.Garment.Wick MS.Dock MS.Outlook MS.Emit
open Teller Graft
open scoped Topology ContDiff Interval Classical
variable {I:Type}{G:Gauge}{n d r k ℓ m h p:ℕ}{F K:Mob G}{W J:Flats G}{u x:ℂ}{P g:Coat G}
variable {t y:ℝ}{a e:ℤ}{b c:Bool}

lemma above_τ (h:kPrice F) : pass F r n ↔ ∀ m,Graft.Above false Landau.wfield (n:ℤ) r (F m):= by
    constructor
    · intro hP m w he hh; refine ⟨ ( h m ℝ _ ).smooth (),fun i hi=>?_ ⟩; let j:ℤ:=fieldDim wfield w+i; have hJ : mass w+i = (j.toNat:ℤ) := by change j=_; have he:= Hem.dm w; change 0≤fieldDim wfield w at he; unfold j; omega
      obtain hz := congr_fun ( congr_fun (hP j.toNat (by unfold mass at hJ; unfold j; omega)) m ) w; rw [restrictT,spotted (by omega),t_bud F hJ] at hz; exact hz
    intro hx k hk; ext m l; by_cases hm:( l.length:ℤ )=r; swap; · exact spotsOff hm
    rw [restrictT,Garment.spotted hm]; rcases lt_or_ge (k:ℤ) (mass l) with h1|h1; · exact t_exc h1
    let i:= ( (k:ℤ) - mass l ).toNat; have h2 : mass l + i=k:= by unfold i; omega
    rw [t_bud F h2]; apply ( hx m l (fun x=>Bool.noConfusion x) (by omega) ).start; unfold mass at h2; omega
abbrev Pays (r h:ℕ)(F:Mob G):= kPrice F ∧ pass F r h
abbrev Cards (r h:ℕ)(P:Coat G):= ∀ᶠ i in dotty,Pays r h (P i)
-- Holds at specific time then project.
lemma mint (r d:ℕ) : Train.Heap ( Cards (G:=G) r d ) where
 zero:= by refine Eventually.of_forall (fun _=>⟨Form0.zero (b:=true)|>.price,fun i H=>?_⟩); rw [restrictT, Pi.zero_apply,Hem.tad0,map_zero]
 add := fun f g h hp=> by filter_upwards [h,hp] with i ⟨hl,h'⟩ ⟨hg,H⟩; refine ⟨ Rock.fall_add hl hg, fun k hk=>?_⟩; rw [ Pi.add_apply,restrictT,t_plus hl hg,map_add,show spot (r:ℤ) _= _ from h' k hk,show spot (r:ℤ) _=_ from H k hk, add_zero ]
lemma scales (h:Cards r d P)(x:ℂ): Cards r d (x • P):= by filter_upwards [h] with i ⟨hx,h⟩; refine ⟨ cost_k hx x,fun k hK=>?_ ⟩; rw [ Pi.smul_apply, restrictT,t_pose,map_smul,show spot (r:ℤ) _=0 from h k hK,smul_zero ]
lemma paysA (h:SeedP ( Cards r p ) W): Ahead r p W:= fun l hl i=> (h i).mono fun _ hi=> hi.2 l hl
lemma age (h:Merg W)(hp:Ahead r p W): SeedP ( Cards r p ) W:= fun i=> by filter_upwards [(h i).price, (eventually_all_finset (Finset.range p)).mpr (fun j hj=> hp j (Finset.mem_range.mp hj) i)] with k hV ht; exact ⟨hV,fun q h=> ht _ (Finset.mem_range.mpr h) ⟩
-- cycle: strictly lower rank for any Wick contract.
lemma via_c (u:ℕ)(hx:ClockD b a r W)(H:Stay n W): SeedP (Cards r u) (step0 G W):= by
    obtain hm:= mine (r:=(r:ℤ)) hx H; intro i; filter_upwards [ (hm.eye i).cap, ( Moony.toast (clockMoon hm.eye) i).price ] with j hj h' ; change Issue _ _ at hj; refine ⟨h',fun k hk=>?_ ⟩; rw [restrictT, spot_tad, show spot (r:ℤ) _=_ from ?_, tad0]; ext a l; by_cases he:(l.length:ℤ)=r; rw [Garment.spotted he]; exact hj a l (by omega); exact spotsOff he
-- for tree
lemma join_width (G:Gauge)(m:ℕ)(i j:Cfield G m)(H:3<wfield i + wfield j) : (A0 G 0 m) i j=0:= by
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,c⟩ <;> norm_num [Landau.wfield,Landau.dim] at H; all_goals funext p; all_goals simp [Wick.A0,Landau.choir,line]
lemma via_tree {k:ℕ}(hz:Merg J)(ht:Merg W)(he:Cap r J)(hp:Cap n W)(hv:k+2=r+n)(hJ:Ahead r 4 J)(hW:Ahead n d W) : SeedP ( Cards k (d+1) ) ( drive0 G J W ):= by
    obtain hL:= age hz hJ; obtain hr:= age ht hW; refine ( mint k (d+1) ).explo _ _ _ (fun i j=>?_); apply Eventually.mono ( (hL i).and ( (hr j).and ((he i).and (hp j)))); intro t ht; rcases ht with ⟨⟨hl,hJ⟩,⟨ha,H⟩,hm,hx⟩; change Issue _ _ at hm hx; let U:=A0 G 0; have hr':= (c_bo (G:=G) 0 (b:=true)).price; have hK:kPrice (arbor U ( J i t ) (W j t)):= by convert! for_tree hl ha (u:=fun _:Unit=>U) (fun m p q=>railto (hr' m p q)) (fun _=>zero_le_one) using 1; simp
    refine ⟨ hK,(above_τ hK).mpr (fun m=>?_ ) ⟩; apply (show Graft.Above false wfield ( (4:ℤ)+(d:ℤ)-3 ) k ( _ )→_ from ?_ ) (Graft.joint_wire ( (above_τ hl ).mp hJ m) ( ( above_τ ha ).mp H m ) ( reverse_a G 0 m ) ( hm m ) ( hx m ) ( join_width G m ) ?_ hv );
    · intro P; rw [(show (↑(d+1):ℤ)=4+d-3 from (by omega))]; exact P
    exact fun i j=> ( hr' m i j 0 ).smooth ()
end YM.FVA2.TreeT
