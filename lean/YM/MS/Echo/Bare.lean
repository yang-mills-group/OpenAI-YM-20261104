import YM.MS.Fleet.Closure
/-!
# BV separation of mark stencils on the infinite lattice cover
Derivation before regression using actual translated stencil, or detailed closure by
all sufficiently large mesh-equivalent cylinder identities. Spatial site units here. No continuum
Taylor-cancellation on supports; keep this separation at all later resets through given order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Puff Puff.SplitP Puff.Engine Puff.Actors Fleet
open scoped Topology ContDiff Interval
variable {p:Team}{G:Gauge}{F H X:Dot G Cover}{h k u:ℤ}
local notation "B"=> Spectrum G
local notation "Θ"=> DotFlip (G:=G)
local infixl:70 " ⋆ "=> couple DotFlip
lemma pulseLeib (hF:Tuned F 0)(hx:Tuned X 0): (B).touch X ( F ⋆ H )=((B).touch X F ) ⋆ H + F ⋆ ( (B).touch X H ):= by
   apply (enterEq _ _).mp; filter_upwards [dutyBV_root B X ( F ⋆ H ) false, dutyBV_root B X F false, dutyBV_root B X H false] with n hF0 ht hp;
   have hv (f g:Dot G Cover): duty false n ( f ⋆ g )= product Θ (duty false n f) (duty false n g):= congr_arg (·.val) (transport_comes (wrap n) (p:=parity) f g)
   change duty false n _= duty false n _; rw [ hF0,map_add,hv,hv,hv,ht,hp ]; refine Balanced.paired (Bonded.costs (( B ).district )) ?_ ?_
   · change Pure (field parity) false (sumHome (shown n X)).val; simp_rw [ total_uses,sum_stack ]; exact Pure.sum _ fun i _=> (move_tie (fun x:Site n=> i+x)).pure _ ( (move_tie (wrap n)).pure _ ( hx.parity ghostParity ) )
   exact (move_tie (wrap n)).pure _ (hF.parity ghostParity)
abbrev Pieces (F:Dot G Cover)(s:Finset Cover): Prop:= BoundBy (s:Set Cover) F
local notation "NG"=> Branch G Axis
lemma support_move {s:Finset Cover} (h:Pieces F s) (p:Cover) : Pieces (Lab.Shift p F) (s.image (fun x=> p+x)):= by unfold Pieces; rw [coe_image]; exact relax F h _ -- variable s
lemma lap_dens (p:Cover): Lab.Shift p ( ( B ).Lap F )=( B ).Lap (Lab.Shift p F):= by simp_rw [Bonded.lap_at,map_sum,map_smul,heart_shift]
lemma touch_dens (p:Cover): Lab.Shift p ( ( B ).touch X F )= ( B ).touch X (Lab.Shift p F):= by
   apply (markEq ..).mp; filter_upwards [soon_root B X ( Lab.Shift p F ), soon_root B X F] with n hn he; have hv (F:Dot G Cover): shown n (Lab.Shift p F)= Lab.Shift (wrap n p) ( shown n F ):=trans_shift ..; rw [ hn, hv,hv, he ]; simp_rw [Bonded.touching,map_sum,map_smul, root_shift] -- symmetry equal.Current root shift holds finite.
variable {S T:Set Cover}{s t:Finset Cover}
lemma couple_ok (h: BoundBy S F)(he:BoundBy T H): BoundBy ( S∪T ) ( F ⋆ H ):= ( h.mono (Set.preimage_mono Set.subset_union_left) ).pair ( he.mono (Set.preimage_mono Set.subset_union_right))
lemma piece_act (h: Pieces F s)(hx: Pieces H t): Pieces ( F ⋆ H ) (s∪t):= (by unfold Pieces; rw [Finset.coe_union]; exact couple_ok h hx)
lemma lap_sep (hF:Tuned F 0)(h:Pieces F s)(hx:Pieces H t) (hu:Disjoint s t): ( B ).Lap ( F ⋆ H )= ( B ).Lap F ⋆ H+ F ⋆ ( ( B ).Lap H ):= by
    -- compare local at support, Lap read separately even when outside. Pair exact left even.
    let x:= s∪t; have hg:Pieces F x:= h.mono (Set.preimage_mono ( Finset.coe_subset.mpr Finset.subset_union_left )); have hz:Pieces H x:= hx.mono (Set.preimage_mono ( Finset.coe_subset.mpr Finset.subset_union_right ));
    simp_rw [ Bonded.lap_at, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, ← Finset.sum_add_distrib ]; apply Finset.sum_congr rfl; intro i _; rw [ ← smul_add ]; refine congr_arg (( B ).fee i • ·) ?_; let m: NG:= (B).plain i; let n: NG:= (B).dual i; rw [heart_by _ _ F hg, heart_by _ _ H hz,heart_by _ _ _ ( piece_act h hx ), map_sum,map_sum,LinearMap.sum_apply,← Finset.sum_add_distrib ]; refine Finset.sum_congr rfl fun j hj=> ?_; let a:LightMode G Cover:= ( n,j ); let b:LightMode G Cover:= (m,j); let U:= F.val; let V:= H.val; have hc:Pure Θ false U:= hF.parity ghostParity; have ht:=link_even ( b:=true ) ( v:=V ) ( diffPair a b ) hc; suffices he: link ( diffPair a b ) true Θ U V=0 by rw [he, zero_add] at ht; exact Subtype.ext ht
    rw [link_pair_left a b ?_ _ hc]; by_cases he:j∈s;
    · have ht:j∉t:= fun q=>Finset.disjoint_left.mp hu he q; rw [show D a V=0 from hx.off ht, show D b V=0 from hx.off ht]; simp
    rw [ show D a U=0 from h.off he, show D b U=0 from h.off he ]; simp
    exact ( B ).op i
end YM.MS.Echo
