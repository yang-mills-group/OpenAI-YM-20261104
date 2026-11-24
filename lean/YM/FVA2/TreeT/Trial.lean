import YM.FVA2.TreeT.Vita
/-!
 # Low-momentum-tree theorem of the pole program

 Collects at the HIGHEST rank through a consistent `Found` criterion. Resolvent
 eigenvalues for the Taylor projectors come before killing impure rank at tree.
 We use cumulant solutions with all auxiliary dimensions from same counterterm
 family (no choosing projection order anew when looking at pole coefficients).
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Landau MS.Arts MS.Arc MS.Plane.Wire MS.Rock MS.Rock.Path MS.Rock.Oceans MS.Plum MS.Alps MS.Garment MS.Color
open _root_.YM.MS.Shine MS.Hem MS.Hem.Mell MS.Train MS.Pearl MS.Motif MS.Heat.Signal MS.Book MS.Book.Convolve MS.Garment.Wave MS.Garment.Wick MS.Dock MS.Outlook MS.Emit
open Teller
open scoped Topology ContDiff Interval Classical
variable {I:Type}{G:Gauge}{n d r k ℓ m h:ℕ}{K:Mob G}{Y:I→Mob G}{F W J:Flats G}{x:ℂ}{P:Coat G}
-- `lower` all auxiliary ℓ compatible even when poles
abbrev restrictT (r h:ℕ)(F:Mob G):=spot (r:ℤ) (Tad F h)
def Ahead (r h:ℕ)(Y:Flats G): Prop:= ∀ j< h,∀ ℓ:ℕ, (fun i=>restrictT r j (Y ℓ i))=ᶠ[dotty] 0
local notation "Q"=> spot (r:ℤ)
local notation "O"=> restrictT r
abbrev pass (F:Mob G)(d:ℕ)(k:ℕ): Prop:= ∀ i<k, restrictT d i F=0
-- let Lean know these are pending at particular degree. Need trailing sector COMBINED.
variable (hx: Joint h J F (fun _:ℂ=>K) P)(hp:Ahead r (h+1) J)
include hx hp
lemma erases (j ℓ:ℕ)(hv:j≤h)(he:ℓ≠0 ∨ j≠h) : ∀ᶠ i in dotty,restrictT r j (F ℓ i)=0 := by
    have hu : ∀ᶠ i in dotty, vamp i h ℓ+j ≠0:=by
       rcases he with he|he; exact (vamp_room h ℓ (Nat.pos_of_ne_zero he)).mono fun i hi=> hi j (by omega)
       obtain ⟨R,hR,H⟩:=Vamp_m he ℓ; exact ( (show ∀ᶠ i in dotty,i∈disc R from dotty_bill hR)).mono fun i hi=> H i hi
    filter_upwards [hu,hp j (by omega) ℓ, (hx.wet ℓ).price, hx.advance] with i hi h0 hℓ hA; obtain he:= hA ℓ; change restrictT r j (J ℓ i)=0 at h0; unfold restrictT at h0 ⊢; rw [ trail_tad he hℓ j,map_smul ] at h0; exact (smul_eq_zero.mp h0).resolve_left hi
lemma answer : Ahead r h F:= fun i hi ℓ=> erases hx hp i ℓ hi.le (Or.inr hi.ne)
omit hx hp in
lemma wind_spot {L:Filter I} (r:ℕ)(hz:Shine.Wind Y L K): Shine.Wind (fun i=>spot (r:ℤ) (Y i)) L (spot (r:ℤ) K):= by
    intro m w; by_cases ht:w.length=r; simp_rw [spotted (by omega: (w.length:ℤ)=r)]; exact hz m w; simp_rw [spotsOff (by omega : (w.length:ℤ)≠r)]; exact tendsto_const_nhds
lemma highest : ∀ᶠ i in dotty,restrictT r h (F 0 i)=Q (K+P i):= by
    filter_upwards [ (hx.wet 0).price, (eventually_all_finset (Finset.range h)).mpr (fun i hi=> answer hx hp i (Finset.mem_range.mp hi) 0), hx.sip ] with i hi hL hU
    refine (Shine.Wind.unique (F:=restrictT r h (F 0 i)) (white_w (F 0 i) h hi (fun j hj=> hL j (Finset.mem_range.mpr hj))) ?_); have hV:= wind_spot r (Y:=fun t:ℝ=> plow (-(h:ℂ)) t (F 0 i)) (K:=K+P i) hU; simp_rw [spot_plow] at hV; exact hV
lemma parade (hv:n≤h) (s y:ℝ): ∀ᶠ i in dotty, restrictT r n (Parade F h y s i)= if n=h then Q (K+P i) else 0 := by
    let U:= insert 0 F.support; rw [ Page U (subset_insert ..) ]; let B(j:ℕ)(x:ℂ):= hikeP x h j y s (F j x); have h0(j:ℕ): ∀ᶠ i in dotty, restrictT r n (B j i)= if j=0∧n=h then Q (K+P i) else 0:= by
       simp_rw [B,ew]; unfold restrictT; filter_upwards [(hx.wet j).price,highest hx hp,(show ∀ᶠ i in dotty,j=0∧n=h ∨ restrictT r n (F j i)=0 from if hP:j=0∧n=h then Eventually.of_forall fun _=> Or.inl hP else (erases hx hp n j hv (by omega)).mono fun _=> Or.inr )] with i hi hx hp; rw [t_pose,Tad_scale hi,map_smul,map_smul]; obtain hx'|hx': n=h ∨ n≠h:= Classical.em ..
       · subst n; rw [neg_add_cancel, ( show Alps.amount 0 s=1 from by simp [Alps.amount]),one_smul]; by_cases he:j=0; subst j; rw [(show weight i 0 _=1 from by simp [Pearl.weight,Alps.amount,Hem.Mell.toll]),one_smul,if_pos ⟨ rfl,rfl⟩]; exact hx
         rw [if_neg (fun p=> he p.1),show spot _ _= _ from (hp.resolve_left (fun p=>he p.1)), smul_zero]
       rw [if_neg (fun p=> hx' p.2),show spot _ _= _ from hp.resolve_left (fun p=>hx' p.2),smul_zero,smul_zero]
    filter_upwards [ (eventually_all_finset U).mpr (fun i _=> h0 i), (eventually_all_finset U).mpr (fun j _=> (hx.wet j).price) ] with i hi hI
    rw [ Finset.sum_apply ]; unfold restrictT; rw [sumT _ (fun j hj=> (show kPrice ( hikeP i h j y s ( F j i )) from cost_k (powder ( hI j hj ) _ s ) _)) n, map_sum, Finset.sum_eq_single 0 ]; · exact ( (hi _ (mem_insert_self ..)): restrictT r n (B 0 i)=_).trans (by simp)
    · intro a ha ht; exact (hi a ha).trans (if_neg (fun h=> ht h.1))
    simp [U]
omit hx hp
private lemma Lift_tad {F:Coat G}(ht:Shine.Lift F K)(r d:ℕ): Shine.Lift (fun i=> restrictT r d ( F i )) (restrictT r d K):= by
    refine (show Shine.Lift _ (Tad K d) from ?_).spotX (r:ℤ); obtain ⟨a,R,hR,H,hx,rfl⟩:=ht; exact ⟨_,R,hR,tad_hol a H d,hx.mono fun i hi=> congr_arg (fun A=> Tad A d) hi,rfl⟩
include hx hp
lemma no_pole : (fun i=>Q ( P i ))=0:= by
    have ht := ( Lift_tad (live0 (s:=0) (y:=0) hx.toll) r h ).wind
    refine deep_zero ( coolC Q hx.ice ) (F:=restrictT r h (hereZ h F 0 0)-Q K) ?_; intro m l; refine ( show Tendsto _ _ (𝓝 (_ - Q K m l)) from (ht m l).sub_const ( Q K m l ) ).congr' (( parade hx hp (le_refl h) 0 0 ).mono fun i hi=>?_); rw [ if_pos rfl,map_add] at hi; dsimp only; rw [ hi ]; simp
-- tree conclusion on `Parade`.
lemma dim_jet (hv:n≤h)(s y:ℝ) : restrictT r n (hereZ h F s y)= if n=h then Q K else 0:= by
    have ht := ( Lift_tad (live0 (s:=s) (y:=y) hx.toll) r n ).wind
    refine ht.unique (Shine.Wind.congr (A:=fun _:ℂ=> if n=h then Q K else 0) (fun _ _=> tendsto_const_nhds) ?_); filter_upwards [parade hx hp hv s y] with i hi; rw [hi,map_add,( show Q (P i)=0 from congr_fun (no_pole hx hp) i ),add_zero]
lemma dim_initial : ∀ᶠ i in dotty,restrictT r h ( F 0 i )=Q K:= (highest hx hp).mono fun i hi=> by rw [hi,map_add,show Q (P i)=0 from congr_fun (no_pole hx hp) i,add_zero]
end YM.FVA2.TreeT
