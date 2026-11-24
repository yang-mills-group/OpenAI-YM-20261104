import YM.OPE.Loom.Tail
import YM.OPE.Loom.Traffic
import YM.OPE.Eye.Remit
/-!
# Pass to fixed-horizon origin matches, uniform for all required tori on F.fuse;
permit moving columns from the X-space estimate along subfilters thereof; extend
to generic exteriors after. Functions prove a result of the signed-source
calculation itself (from `Sharper` physical estimates), independently of
whether one has succeeded in achieving the remaining polylog parameter weights
through all limiting physical columns. Adapted from Sweep.Camp and Eye.Remit
and works even for thicker group beyond an M-horizon halo.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set MeasureTheory
open scoped Topology BigOperators Classical
namespace YM.OPE.Loom
open Lattice RG Wilson MergeProof Accent Ribbons Source Overlay Bid ManyCopies Next.Rank Next.UVStress PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Push Marker Cells Extraction
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{T:Table C.book}(F:Spec.Final C f T){W r D}(A : Sharper C W r D)
local notation "Y" => C.path.levels
local notation "X" => C.path.levels.clock.hatBeta
local notation "δ" => renal C.path.levels
local notation "ψ" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "P" => C.path.levels.budget
set_option quotPrecheck false
variable {p : ℕ}{α : Type} [Fintype α][DecidableEq α]{𝓛:Filter (ℕ×ℕ)} {k m j K d t:ℕ} {v:ℝ}{x:α→ Cover}
lemma vista (x : Cover) : ∀ᶠ i:ℕ×ℕ in f.fuse,C.S.place (wrap (C.side j i.2) x)=C.S.gridPoint j x:= by
   rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [f.per.cofinal.eventually (faraway C j x)] with i hi using Eventually.of_forall fun _=>hi -- lint
lemma grid_minus (x y: Cover)(S:Schedule) : S.gridPoint j (x-y)= S.gridPoint j x-S.gridPoint j y:= by ext i; change S.a j*((x i-y i:ℤ):ℝ)=S.a j*x i-S.a j*y i; push_cast; ring
variable (w:α→ℝ) (s:α→ C.book.Token)(u:ReadLabel C s)
structure RootMark (C:Family G)(t k j m K d:ℕ)(v:ℝ)(r:ℕ→ℕ)(s:α→ C.book.Token) (x:α→ Cover)(i:α) : Prop where
   gate : Gate (α:=α) C r t k j m v
   walks : k+1 < j
   units : x i=0
   high l : ‖C.S.gridPoint j (x l)‖ ≤ v*t
   low (h a:α)(hp:h≠a) : 4*v ≤ ‖C.S.gridPoint j (x h)- C.S.gridPoint j (x a)‖
   aisle l : 8*‖C.S.gridPoint j (x l)‖≤ C.S.a m
   opens : Stock.Tabs.opens C.path.levels 1 m K
   tempo : K≤ k
   money : 0<t
   state : C.ref d≤K
   slots l : C.ref (s l).1 ≤ j
   fits : GridApprox.room C.path.levels m k (lensScope C d)
local notation "ρ" => purse C w j k t
local notation "e" => (ebb C d k ρ)
local notation "p₀" => bid C d K k ρ
variable (i:α)(HE:RootMark C t k j m K d v r s x i)
variable (hp:∀ l,0<w l) (hM:∀ a,∀ᶠ l:ℕ×ℕ in 𝓛, w a*Spindle.paid C (s a).1 j l.1 l.2 (u a l) ≤ fly (G:=G) C.path.levels (s a).1 j) (hx:𝓛≤f.fuse)
local notation "N" => (fun z:ℕ×ℕ=> ∀ (i:ℕ), i ≤ z.1)
include A F HE hM hx hp
lemma credited : ∀ᶠ l:ℕ×ℕ in 𝓛, ∃ z:C.label d, quota C d k l.1 l.2 z ≤ 2*e ∧ Cards.PaidAt C.S l.1 l.2 m (C.beta l.1 l.2) (2*(stakes C m K/p₀)) (Cards.register C j x (germ u) l.1 l.2 - C.O l.1 l.2 z 0):=by
   have hd:= ((Cards.largeMesh f).mono_left hx); have hh:=F.room.cutoff
   filter_upwards [eventually_all.mpr (fun l:α=> hd.eventually (near_center C m (s l).1 hh)), hd.eventually (near_center C m d hh), hd.eventually_gt_atTop j,eventually_all.mpr (fun a:α=> hM a),eventually_all.mpr (fun l:α=> (vista (C:=C) (j:=j) (x l)).filter_mono hx), eventually_all.mpr (fun a:α=>eventually_all.mpr (fun l:α=> (vista (C:=C) (j:=j) (x l-x a)).filter_mono hx))] with l hR hD hK' hm hQ hF
   let a:=(wrap (C.side j l.2)) ∘ x; have hu:j< l.1:= hK'; have hg:= HE.walks.le; have hk:= HE.opens.1.trans HE.tempo; have hb:=hk.trans (k.le_succ.trans (hg.trans hu.le)); let E:= center C.S l.2 hb 0; let Q k:= C.O l.1 l.2 (u k l) ((C.S.toDepth hu.le l.2).embed (a k))
   have he(l' a':α): C.S.place (a l'-a a') = C.S.gridPoint j (x l')-C.S.gridPoint j (x a'):= by unfold a; simp_rw [comp_apply,← map_sub]; exact (hF _ _).trans (grid_minus ..)
   have hZ(k): Interior (E.chamber 0) (Q k):= hR k hb l.2 _ (by rw [C.S.embeds_place]; change 8*‖C.S.place (wrap (C.side j l.2) (x k))‖ ≤ _; rw [hQ k]; exact HE.aisle k) _
   have hd'(v:C.label d): Interior (E.chamber 0) (C.O _ _ v 0) := hD hb l.2 _ (by rw [latzero]; simp [(C.S.a_pos _).le]) _
   have hE: a i=0:= by unfold a; rw [comp_apply,HE.units,map_zero]
   obtain ⟨z,hq,hP,hV⟩ := gate_consumer a A hk HE.walks HE.gate (fun l'=> (show ‖C.S.place (a l')‖ ≤ _ from by exact (congrArg (‖·‖) (hQ _)).trans_le (HE.high _))) (fun i j hp=> (congrArg (‖·‖) (he i j)).symm ▸ HE.low i j hp) w _ (fun i=>u i l) hh d K HE.money HE.state HE.tempo HE.opens HE.slots hm hp hu HE.fits i hE Q (fun _=>rfl) hb hZ hd'
   refine ⟨z,hq,?_⟩; rw [show Cards.register C j x (germ u) _ _=(fun U=>∏ i,Q i U) from ?_]; exact ⟨hb,hP,hV⟩
   funext U; rw [germ_here]; dsimp only [Q]; simp_rw [Cells.location,dif_pos hu.le]; rfl
structure MatchesHere (f:Filter (ℕ×ℕ)) (k j d m:ℕ) (u:ReadLabel C s)(x:α→ Cover)(z:C.label d) (σ τ:ℝ) :Prop where
   buys : ∃ (φ:Filter (ℕ×ℕ))(q:ℕ×ℕ→ C.label d), φ.NeBot ∧ φ ≤ f ∧ Tendsto q φ (𝓝 z) ∧
      ∀ᶠ i:ℕ×ℕ in φ, quota C d k i.1 i.2 (q i) ≤ σ ∧ Cards.PaidAt C.S i.1 i.2 m (C.beta i.1 i.2) τ (Cards.register C j x (germ u) i.1 i.2 - C.O i.1 i.2 (q i) 0)
lemma viable [𝓛.NeBot] : ∃ z:C.label d, MatchesHere s 𝓛 k j d m u x z (2*e) (2*(stakes C m K/p₀)):= by
   let p (l:ℕ×ℕ)(z:C.label d):= quota C d k l.1 l.2 z ≤ 2*e ∧ Cards.PaidAt C.S l.1 l.2 m (C.beta l.1 l.2) (2*(stakes C m K/p₀)) (Cards.register C j x (germ u) l.1 l.2 - C.O l.1 l.2 z 0)
   let z i:= if h:∃ v,p i v then h.choose else 0; have he:∀ᶠ i in 𝓛,p i (z i):= (credited F A w s u i HE hp hM hx).mono (fun i h=> by unfold z; rw [dif_pos (show ∃ v,p i v from h)]; exact Classical.choose_spec _)
   obtain ⟨Q,hQ,hI⟩ := quota_stop C F.room.cutoff (HE.state.trans HE.tempo); obtain ⟨χ,hχ,hX,v,hY⟩:= finite_extract (𝓛:=𝓛) z (Q*(2*e)) (by filter_upwards [he,((Cards.largeMesh f).eventually_ge_atTop k).filter_mono hx] with i hi hm using (hI i.1 i.2 (z i) hm).trans (mul_le_mul_of_nonneg_left hi.1 hQ))
   exact ⟨v,χ,z,hX,hχ,hY,he.filter_mono hχ⟩
end YM.OPE.Loom
