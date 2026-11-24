import YM.RGLocalTaylor.Retain.Read
/-!
# Grade-one unmarked responses and panel compatibility
Identify the only low-order uses of the transmission aperture EXACTLY.
Pricing after that happens linearly. No equations comparing R(S).heat or
post choices, and no claims of propagation of marked READ posture through
 ZERO activity addresses left in place. Loom.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt RG01.Survive
open Mayer Fort goodK Mill
open Match Song Push AnalyticBridge VerifiedReset Collection Extra.Iteration Refrain Geo Quotes
open Captain Ursell Gas Height Brim
open Laminate
namespace Gorge
variable {M:ℕ} (H)(p:H.ThinP)(tp:Stencils T M) (take:H.fragrances→ℕ→Prop) (ξ : Post.glyph G f)
set_option quotPrecheck false
local notation "κ" => Opacity.key S

lemma lengthLease (u:Orders M) (V:Config G c)(hh:cover H tp (χ:=χ) p u V≠0): p.val.Nonempty ∧ p.val.card ≤ u.val:=by
   have he : (H.unionP p.val).Nonempty:= p.2.1; refine ⟨?_,?_⟩ -- nonempty.direct
   · obtain ⟨v,h⟩:=he; obtain ⟨i,hi,ht⟩:= mem_biUnion.mp h; exact ⟨i,hi⟩
   unfold cover Mill.Total at hh; split at hh
   next ht=>
      obtain ⟨i,hi,hF⟩:= Finset.exists_ne_zero_of_sum_ne_zero hh
      rw [← (show decorOrder i= u.val from (mem_filter.mp hi).2)]
      let F:= fun (_: ↥p.val)=> (1:ℕ)
      calc
        _ = ∑ x:↥p.val,F x := by simp [F]
        _ ≤ _:= sum_le_sum (fun j _=> by show 1 ≤ (i j).val+1; omega)
   exact False.elim (hh rfl)

lemma view_leg (u:Decors p.val M) (h:∀ x∈p.val,x∉Set.range (Opacity.key S)) : parcel (physical H M) p.val (leg H (own p.val)) u= parcel (mantle H ξ M) p.val (leg H (own p.val)) u:=by
   change Insert.mk _=Insert.mk _; congr! 1; funext F X z; refine prod_congr rfl fun x hx=>?_ ; simp_rw [payloadT,dif_pos hx,Fort.keepsOff H _ _ _ (h x hx)]
lemma view_fit (h:∀ x∈p.val,x∉ Set.range (Opacity.key S))(y:Orders M): cover H (physical H M) p y (χ:=χ)=cover H (Fort.mantle H ξ M) p y (χ:=χ):= by
   unfold cover Mill.Total; split; next hz => exact funext fun V=> Finset.sum_congr rfl (fun i _=> by rw[view_leg H p ξ i h])
   rfl

variable {z:H.fragrances}
lemma view_clean (h:∀ q x,x∈(z.2 q).val→x∉Set.range (Opacity.key S)):
    Read.field take (cover H (physical H M) (χ:=χ)) z=Read.field take (cover H (mantle H ξ M) (χ:=χ)) z:= by
   ext V; unfold Read.field; exact congr_arg _ (sum_congr rfl fun q _=> prod_congr rfl fun i _=> congr_fun (view_fit H _ ξ (h i) (q i)) V )
lemma columnDebt {V:Config G c}(t:lot z (Orders M))(he: aliquot (cover H tp (χ:=χ)) z t V≠0): breadth H z ≤ atGrade (z:=z) t ∧ ∀ j,(z.2 j).val.Nonempty := by
   have hp i:= lengthLease H (z.2 i) tp (t i) (χ:=χ) V
   have hx i:=hp i (fun h=> he (prod_eq_zero (mem_univ i) h))
   exact ⟨sum_le_sum (s:=univ) (fun i _=> (hx i).2),fun i=>(hx i).1⟩
lemma one_supported (hz : z ∉ Set.range (icon H))(h:∀ n,take z n→ n≤1):
    Read.field take (cover H (physical H M) (χ:=χ)) z=Read.field take (cover H (mantle H ξ M) (χ:=χ)) z:= by
   by_cases ht:∀ q x,x∈(z.2 q).val→ x∉Set.range (Opacity.key S); exact view_clean H take ξ ht
   push Not at ht; obtain ⟨i,x,hK,v,rfl⟩:=ht
   have hZ (A:Stencils T M): Read.field take (cover H A (χ:=χ)) z=0:= by
      ext V; unfold Read.field; rw [Finset.sum_eq_zero (fun t ht=> ?_),mul_zero];rfl
      by_contra hv; have hh:=columnDebt H A (χ:=χ) t hv; exact hz ⟨v,(Beam.lantern z (fun i=> Finset.card_pos.mpr (hh.2 i)) (hh.1.trans (h _ (mem_filter.mp ht).2)) i hK).symm⟩
   rw [hZ _,hZ _]

lemma not_of_booth (p:Meadow.Poet H)(i) : ∀ x, x∈ ((Meadow.booths H p).2 i).val→ x∉Set.range κ := by
   rintro x hx ⟨v,hv⟩; subst x; have hx : κ v ∈ Deck.Mint.hatch S (p.val.2 i):= hx; obtain ⟨y,_,hy⟩:= mem_map.mp hx
   rcases y with y|y|y|y <;> simp only [Deck.Mint.disc,Opacity.key,Deck.Mint.album,Deck.Mint.note,Sum.elim,Embedding.coeFn_mk, Function.comp_apply, Sum.inl.injEq, Sum.inr.injEq] at hy <;> contradiction
lemma not_of_pennies {V:Magazine H} (h : V∈ Meadow.bouquet H k){i} (he: V=Sum.inl i): ∀ j x,x∈(i.2 j).val→x∉Set.range κ:= by
   rw [he,Meadow.bouquet] at h; obtain ⟨v,hv,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp h); exact not_of_booth H v
-- across identity Furrow (necessary from latch Reader)
lemma view_body {J:Rep G f} {X :Cash W s μ L Q o C T J} (Y : Match.Alliance H X 1 0) (ht:Y.units=Equiv.refl (Molecule S)){u:H.fragrances} (hv:(Sum.inl u:Magazine H)∈ Meadow.bouquet H k)
   (take: X.fragrances→ℕ→Prop) : Read.field take (cover X (physical X M) (χ:=χ)) (Y.furrow u)=Read.field take (cover X (mantle X ξ M) (χ:=χ)) (Y.furrow u):= by
   have hw:= not_of_pennies H hv rfl
   rcases u with ⟨j,v⟩; let w i:= Y.bearing (v i)
   change Read.field take (cover X (physical X M) (χ:=χ)) ⟨j,w⟩ = Read.field take (cover X (mantle X ξ M) (χ:=χ)) ⟨j,w⟩
   refine view_clean X take ξ ?_
   intro i x hx; have h:x∈Y.units (v i).val:=hx
   rw [ht] at h; exact hw i x h

lemma issued (h:∀ z n,take z n→ n≤ M): Read.field take (cover H (physical H M) (χ:=χ)) = Read.field take (Mayer.issue H χ M):=by
   ext z V; unfold Read.field; apply congr_arg; apply Finset.sum_congr rfl; intro q hq
   have hx:= h z _ (mem_filter.mp hq).2; exact Finset.prod_congr rfl (fun i _=> congr_fun (Mill.roleBase H (p:=z.2 i) (τ:=q i) (χ:=χ) ((Mill.total z q Fin.val i).trans hx)) V)

variable (i:ℕ)
lemma icon_auth : authorized H (head i):=by
   refine ⟨⟨singleton_nonempty _,fun a ha b hb=>?_⟩,(pistil (T:=T) (R:=R) i ..).1⟩; rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl
lemma fareAt : Laminate.tax (icon H i)=1:=by
   suffices hh: Ursell.coefficient H.seam (icon H i).2=1 by unfold Laminate.tax; rw [hh]; change 1/(((1:ℕ).factorial):ℝ)=(1:ℝ); norm_num
   unfold Ursell.coefficient
   let v: Option (Fin 0)→H.ThinP:=fun _=>once H i; have he : pot H.seam v=∅:=by
       apply Finset.eq_empty_iff_forall_notMem.mpr; intro p hp; have h := (potential_mem H.seam v p |>.mp hp).1; have hv : p.card ≤ 1:= (Finset.card_le_univ _).trans (by simp); omega
   change Graph.mass (pot H.seam v)=1; rw [he]; unfold Graph.mass; have hh : Graph.reaches (∅: Graph.Network (Option (Fin 0))) := by intro i j; rw [Subsingleton.elim i j]
   have he : Graph.connectedGroups (∅:Graph.Network (Option (Fin 0)))={∅}:=by ext i; simp only [Graph.belongs,Finset.subset_empty, Finset.mem_singleton]; exact ⟨And.left,fun e=> e.symm ▸ ⟨rfl,hh⟩⟩
   rw [he]; simp [Graph.alternating]
local notation "F'" => icon H i
lemma lonely (u:Expansions H M)(k:Orders M)(hs:∀ b, take F' b ↔ b=k.val): Read.field take u F'= u (once H i) k:= by
   ext V; unfold Read.field; let f:lot (icon H i) (Orders M):= fun _=>k
   change Laminate.tax F' * _=_; rw [fareAt,one_mul]; let X:= Option (Fin 0)
   have he(t:lot F' (Orders M)) : atGrade (z:=F') t=(t none).val:=by unfold atGrade; change (∑ i: Option (Fin 0),(t i).val)= _; rw [Fintype.sum_option]; simp; rfl
   letI : Subsingleton (Option (Fin (icon H i).fst)):=inferInstanceAs (Subsingleton (Option (Fin 0)))
   rw [sum_eq_single f]; change (∏ j : Option (Fin 0), u _ _ _)=_; rw [Fintype.prod_option]; simp; rfl
   · intro v hv hh; exact False.elim (hh (funext (fun i=> Fin.ext ((by rw [Subsingleton.elim i none,←he v]; exact (hs _).1 ((mem_filter.mp hv).2))))))
   intro hv; exact (hv (Finset.mem_filter.mpr ⟨mem_univ _,(hs _).2 (he f)⟩)).elim
lemma soloPack (u:Expansions H M)(k:Orders M): Read.field (fun _ b=>b=k.val) u F'= u (once H i) k:= lonely H _ i u k (fun _=>Iff.rfl)
end Gorge
end Retain
end YM.RGLocalTaylor
