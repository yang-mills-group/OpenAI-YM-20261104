import YM.RG05Readout.Halls.Kin
/-!
# Rig for WM aperture from one aligned cover tuple, all cells

Separation paid from actual tree planners including alternative/tie exclusions
on copies. Sources at arbitrary relative placements (not just distinct capture
roots); nuclear factorized supports in physical coordinates. Uses budget spacing
constant.Applicable with large p, n≤m etc. No diagonal credit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Halls
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons Ribbons.ManyCopies
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V][DecidableEq J][Fintype J][DecidableEq I][Fintype I]
    {j b k g ℓ:ℕ}
set_option quotPrecheck false
local notation "S'"=> C.S
local notation "Πξ"=> C.S.toDepth
local notation "ψ"=> C.path.levels.clock
local notation "K"=> C.path.levels.clock.op
local notation "α"=> C.S.a
local notation "G!"=> C.S.gridPoint
local notation "λ!"=> C.side
local notation "ω"=> Lattice.wrap
local notation "Z!"=>C.path.levels.budget
local notation "χ"=> (C.S.radius p)
local notation "X!"=> C.side n p
section
variable (c:J→Site (C.side n p)) (E:J→Motion)(v:V→ Cover)(s:V→ℕ)(W:V→Body)(F:J→Body)(Y:J→I)
local notation "y"=> (fun j:V=>Lattice.wrap (C.side n p) (v j))
local notation "U!" => Unit × Recipe J V
local notation "o"=> roads c E y
local notation "l!"=> side_E E (V:=V)
local notation "V!"=> ManyStem C (roads c E y)
local notation "T₀"=> (Mine.tree (roads c E y) (side_E E (V:=V)))
local notation "s₁"=> toss s d (J:=J)
local notation "H!"=> coats c E y W F
local notation "Z!₁"=> font (V:=V) Y
local notation "Q!"=> partialGroup Unit (basin J V)
local notation "Θ"=> (Many.shadow (T₀) s₁ H! m)
-- trace.Proof
omit [DecidableEq J][Fintype J][DecidableEq V][Fintype V] in
lemma touched (ht:n ≤ m) (j:V! m)(hx:j∉ Θ)(i:V)(he:j.val.fst.snd.snd=producer i) : let k:=j.val.fst.snd.fst
    ∃ (w : Cover)(a b:E4), j.val.2= affine (E k).1 ((C.S.toDepth ht p).embed (c k)) ((ω (C.side m p)) w) ∧ a ∈ Native.box∩ tsupport (W i).val ∧ b∈ Native.box ∧ G! n (v i)+(α n) • a = G! m w+(α m) • b:=by
   intro k; let T:= windF W F ∘ (T₀).labelY n; have hV : windF W F j.val.1=W i:=by unfold windF; rw [he]
   have hY:o j.val.fst= affine (E k).1 (c k) (Lattice.wrap _ (v i)):=by unfold roads;rw[he]
   obtain ⟨w,a,b,hV₁,hQ,hΩ,hZ,hF⟩:= picked o l! T s₁ ht j hx (c k) (v i) hY
   exact ⟨w,a,b,hV₁,⟨hQ,hV ▸ (show a ∈ tsupport (windF W F j.val.1).val from hF)⟩,hZ,hΩ⟩
-- center pawn veto.Even its actual copy participates before
omit [DecidableEq J][Fintype J][DecidableEq V][Fintype V] in
lemma burned_zero (ht:n ≤ m) (j:V! m)(hp:j.val.fst.snd.snd= Basket.center V): j∈ Θ:=by
    by_contra he; let k:= j.val.fst.snd.fst; let T:= windF W F ∘ (T₀).labelY n; have hX : windF W F j.val.1=0:=by unfold windF; rw [hp]
    have hx : o j.val.1= affine (E k).1 (c k) (ω X! 0):=by unfold roads; rw [hp]; simp [affine,k]
    obtain ⟨w,a,b,h₁,h₂,h₃,h₄,hF⟩:= picked o l! T s₁ ht j he (c k) 0 hx; change a∈ tsupport (windF W F j.val.1).val at hF; rw [hX] at hF; change a∈ tsupport (0:E4→ℂ) at hF; simp at hF

omit [DecidableEq J][Fintype J][DecidableEq V][Fintype V] in
lemma partner (ht:n ≤ m)(i j:V! m)(hp: i∉ Θ)(hq:j∉ Θ)(hr:i.val.1≠j.val.1)(hv: (Q!).bunch i.val.1= (Q!).bunch j.val.1): i.val.fst.snd.fst=j.val.fst.snd.fst ∧ ∃ x x':V,i.val.fst.snd.snd=producer x ∧ j.val.fst.snd.snd=producer x'∧ x≠x':=by
    have hx:i.val.1.snd.fst=j.val.1.snd.fst:=congr_arg (fun i':Unit× Root J =>i'.2.1) hv
    have hy:(i.val.1.snd.snd).isLeft=(j.val.1.snd.snd).isLeft:=congr_arg (fun i':Unit× Root J=> i'.2.2) hv
    have ht':i.val.1.snd.snd≠j.val.1.snd.snd:=fun he=> hr (Prod.ext (Subsingleton.elim ..) (Prod.ext hx he)); refine ⟨hx,?_⟩
    let w:= i.val.1.snd.snd; let w':= j.val.1.snd.snd
    have hi:w≠ Basket.center V:= fun h=> hp (burned_zero c E v s W F ht _ h); have hj:w'≠ Basket.center V:= fun h=>hq (burned_zero c E v s W F ht _ h)
    change ∃ x x',w=producer x∧w'=producer x'∧x≠x'; change w.isLeft=w'.isLeft at hy; change w≠ w' at ht'; clear hp hq
    generalize H : w=e at hy hi ht' ⊢; generalize H' : w'=f at hj hy ht' ⊢
    cases e with
    | inl t=>
       cases t with
       | none=> exact (hi rfl).elim
       | some x=> cases f with
             | inl t=> cases t with
                        | none=> exact False.elim (hj rfl)
                        | some x'=> exact ⟨x,x',rfl,rfl,fun h=> ht' (congr_arg producer h)⟩
             | inr w=> exact False.elim (Bool.noConfusion hy)
    | inr t=> cases f with
            | inl t'=> exact False.elim (Bool.noConfusion hy)
            | inr t'=> exact False.elim (ht' (congr_arg Sum.inr (Subsingleton.elim t t')))
variable {R r:ℝ}{t:ℕ}
omit [Fintype I] in
set_option maxHeartbeats 750000 in
lemma inherited (S:Stock.Tabs C.path.levels)(hk:n ≤ m) (hR: ∀ i:V, ‖G! n (v i)‖≤ R*(α n)) (h'p:∀ i:V,separation (y i) 0 ≤ t)
    (hP: 2*(R+2)*(α n)<χ) (hs:carton C n v W r)(ht: 2*(α m)*(1+((Z! m).B:ℝ)^2)<r)
    (he:∀ i j:J, Y i ≠ Y j → (Z! n).B^2+1+2*t ≤ separation (c i) (c j)) : Clearance (o) (l!) (s₁) H! Z!₁ m:=by
    intro T hd i hi j hj hN; have hp: i∉Θ:= fun h=> Set.disjoint_left.mp hd h hi; have hq:j∉ Θ:=fun h=>Set.disjoint_left.mp hd h hj
    let b:=i.val.1; let a:=j.val.1; let u:=b.2.1; let w:=a.2.1
    have hL:Lit Z!₁ (T₀|>.labelY m) T.val:= (Finset.mem_filter.mp T.property).2; have hx:b ≠ a:= fun hv=> hN (hL.2 hi hj hv)
    by_cases hU:Y u= Y w
    · have hξ := (show Clan Y hL.climb.val from (Finset.mem_filter.mp hL.climb.property).2) b (Finset.mem_image_of_mem _ hi) a (Finset.mem_image_of_mem _ hj) hU
      obtain ⟨h,x,x',hy,hz,hΨ⟩:=partner c E v s W F hk _ _ hp hq hx hξ
      obtain ⟨v₁,a₁,b₁,he₁,hZ₁,hV₁,hF₁⟩:=touched c E v s W F hk _ hp x hy
      obtain ⟨v₂,a₂,b₂,he₂,hZ₂,hV₂,hF₂⟩:=touched c E v s W F hk _ hq x' hz
      let t:= pair_verified _ _ v₁ v₂ hk a₁ a₂ b₁ b₂ hZ₁.1 hZ₂.1 hV₁ hV₂ hF₁ hF₂ (hR _) (hR _) hP (hs _ _ hΨ _ hZ₁ _ hZ₂) ht
      change _ ≤ separation i.val.2 j.val.2; rw [he₁,he₂,h]; unfold affine; rw [separation_translate,separation_signed]; exact t
    apply Mine.isolation S hk; have hp₁: (Πξ hk p).parent i.val.2=o b:=i.property hk
    have hp₂:(Πξ hk p).parent j.val.2=o a:= j.property hk
    rw [show ((Πξ hk p).parent ((Mine.tree o l!).supportX m i)) = _ from hp₁, show ((Πξ hk p).parent ((Mine.tree o l!).supportX m j))= _ from hp₂]; have h:= he u w hU; have ht' : separation (c u) (o b)≤t := (separation_comm ..).trans_le (reached c E v t h'p b); have hw: separation (o a) (c w) ≤ t:=reached c E v t h'p a; have hg :=separation_triangle (c u) (o b) (c w); have hg' := separation_triangle (o b) (o a) (c w); omega
-- note may need instantiate T explicitly because shadow typeclass older. 
end
end YM.RG05Readout.Halls
