import YM.MS.Wind.Lead
/-!
# High physical fields coefficient normalization

Frame conversion degree weight triangular; degree-zero corrections strictly lower
 rank on each homogeneous block. Also handles rank 0. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind.Leading
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real Domain
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p:Team}{B:Deck G}{d:ℕ}(V: LitBook B){j:Glyph B d}{F S:Recount G}{P: Acts B d}{n r:ℕ}{u:ℤ}
lemma torch_piece (w: List (Lane4 G))(h:w.length=r)(F:Law G)(j:ℕ): torch j F w= torch j (Book.mask r F) w:= by unfold torch; rw [show fieldVal (Book.mask r F) _= fieldVal F (ray w) from funext fun t=> enough _ (by simp [h])]
lemma excuse {F H: Recount G}{v:ℤ}(h:∀ x w, w.length=r → ∀ j:ℕ, fieldDim wfield w+j≤v → torch j (F n x) w=torch j (H n x) w) (hp:∀ x:Clock ℝ,∀ w, ContDiff ℝ ∞ (fieldVal (F n x) (ray w)))(hh:∀ x: Clock ℝ,∀ w,ContDiff ℝ ∞ (fieldVal (H n x) (ray w))) (hu:u≤v)(i):
   slice (F n-H n) false r u i=0:= by
   funext l; unfold slice; split; swap; rfl
   next ha=>
    have hk t: (skin wfield u ((F n - H n) (i,t))) l=0:= by
        unfold skin; split; swap; rfl
        next h' => rw [Pi.sub_apply, torch_sub l (hp (i,t) l) (hh (i,t) l),h (i,t) l ha.2 _ (by omega), sub_self]
    simp_rw [hk]; exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
lemma guarded (p:Team)(hx:FitOrder j (P 0))(h: PhysicalHF j F)(hr:j.grade ≤ r)(ht:u≤d)(H: Disc false 0 S F 1 d)(y:ℝ): slice ((Seek V p d).wake P 0-F 0) false r u y=0:= by
    refine excuse (F:=(Seek V p d).wake P) ?_ ?_ ?_ ht y
    · intro x w hw i H; let L := (Seek V p d).wake P; have hh:= zerosOrder p V hx x.1
      obtain h1|h1:= lt_or_eq_of_le hr
      · rw [torch_piece w hw (L 0 x), torch_piece w hw (F 0 x), maskOff (v:=r) (by omega) (show Limit (L 0 x) j.grade from hh.1 (exp x.2)),maskOff (u:=j.grade) (by omega) (h.too x)] -- L unfolding rw
      have hc : Form j.read wfield (j.size:ℤ) false:= (lease_one.mp (lease_enough G (B.le (B.form _ _ _)))).2.1; rw [← h1] at hw; rw [torch_piece w hw (L 0 x), face_here (show Lifting.Face wfield (mask j.grade (L 0 x)) j.read j.size false from hh.2 (exp x.2)) (w:=w) (fun u=> Bool.noConfusion u) i (by rw [h.owns]; exact H),torch_piece w hw (F 0 x), h.top, hc.const_term w (fun v=> Bool.noConfusion v)]
    · exact fun x w=> ((aqua V p P).owes 0 |>.stay x.1).joint.routine _ _
    exact fun x w=> (H.master.road ℝ (ray w) 0 (Nat.zero_le _) (fun v=> Bool.noConfusion v) (fun v=> Bool.noConfusion v)).1 x

-- use at any fixed action. preserve leading.
theorem physicalAt (h:G.Simple)(hq:Fixed (col (skyline G p)) F true 4 1) (hh: Disc false 0 F S 1 d)(hx: PhysicalHF j S): ∃ A: Acts B d, FitOrder j (A 0)∧ Fixed (col (horizon V p A)) S false d 0:= by
    let K:=trio V j p; let W:= Seek V p d; let U:= Tactic0 j; let V0:= col (skyline G p); let T:= mark_seek V (p:=p) (d:=d) h -- implicit arg V? #error
    have HT (i:Code U): Spheres wave (spaceL G) V0 (K.wake i) 1 0 false:= T.law _;
    suffices he: ∃ i:Code U, Fixed (K.wake i) S false d 0 by obtain ⟨i,hi⟩:=he; exact ⟨clockM _ i,(i 0).property rfl,hi⟩
    refine assigned (B:=fun _=> V0) HT hh.master hh.good (fun i=>T.occurs (clockM j i)) hh.open' ?_ (by omega) ?_ (script j)
    · intro X n hn hp i hi r; exact hq (n-i) (by obtain he:=path_in hi; omega) _ (fun _ => Nat.succ_pos r)
    intro n hn r hr u hu hv X EE HE
    let M:= K.wake X n-S n; let J:= slice M false r u; have hz:= advanced (HT X) hh.master hn hr EE
    by_cases hk: n=0 ∧ j.grade≤r; · obtain ⟨rfl,H⟩:=hk; refine ⟨X, Move.refl J ?_ ⟩; intro i w _ hx'; change slice _ _ _ _ _ _=_; exact congr_fun (guarded V p (P:=clockM j X) ((X 0).property rfl) hx H hv hh i) w -- J after subst
    have ht : Ready J:= slice_ready hz hv (Ready.sub ((HT X).poly n) (hh.master.poly n));
    have hu' (i:ℝ) : J i∈ Lease G u r 0:= lease_one.mpr ⟨slice_solid hz hv fun t=> ((HT X).trueC n t).sub (hh.master.trueC n t),slice_form hz hv,rank_slice⟩
    have hL (i:ℝ) : natQ (J i)=0:= funext (fun l=> closes (HT X) hh.master hh.good hn hr EE hv HE i l (fun v=>Bool.noConfusion v))
    obtain ⟨a,g,h0,h1,hJ,hI,he⟩:= mark_inter ht hu' hL B; obtain ⟨Q,T,hQ,hT,hW⟩:= Menus.room_here (n:=n) V p (clockM j X) hu hv h0 h1 hJ hI
    let P := Menus.patch (clockM j X) Q T n; have he' : FitOrder j (P 0):= fix_order (P:=clockM j X) ((X 0).property rfl) hQ hT.le (by omega)
    let Y:Code U:= fun i=> ⟨P i,fun h=> h ▸ he'⟩;
    have hm : ∀ i<n,(X i)=(Y i):= fun i hi=> Subtype.ext (hW.past i hi)
    refine ⟨Y, Move.replace (rewind (K:=K) rfl rfl hm (fun i=> (((aqua V p (clockM j X)).owes n).stay i).joint) (fun i=> (((aqua V p P).owes n).stay i).joint) (mark_pay V hW)) (fun i w hw hI=> congr_fun (congr_fun he i) w)⟩ -- remove
end YM.MS.Wind.Leading
