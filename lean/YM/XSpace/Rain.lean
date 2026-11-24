import YM.XSpace.Ice

/-!
# All interior hits at all orders

With no internal contractions left on the aux side, the vanishing tests accept
inside differentiations made with the remaining color-pair probes, avoiding all
reservations for other spectators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Legs
open Function Set Filter MvPolynomial Maxwell Maxwell.Free Next.Rank.Normal
open scoped BigOperators Classical
variable {G : Gauge} {L A : Finset (World G)} {S : Finset E4} {P Q : Pol G}

def outer (S : Finset E4) (G : Gauge):= supported ℂ {x : World G| x.1∉ S}
lemma Friends.outer_fit (h : Friends L S P): P∈outer S G:=by
  induction h with
  | baby=> exact one_mem _
  | @joined S P x y he hf hx hk hl _ ih=>
    exact Subalgebra.mul_mem _ (Subalgebra.sum_mem _ fun a _=> Subalgebra.mul_mem _ (X_mem_supported.mpr he) (X_mem_supported.mpr hf)) ((show outer _ G ≤ outer S G from supported_mono (fun i hh hk=> hh (spots_more x y hk))) ih)
  | add _ _ ha hb=>exact Subalgebra.add_mem _ ha hb
  | smul a h ih=>exact (outer _ G).toSubmodule.smul_mem _ ih
lemma Friends.extendL (h : Friends L S P) (hL : L⊆A): Friends A S P:= by
  induction h with
  | baby=>exact .baby _
  | joined x y h k hm hl ht _ ih=> exact .joined x y h k hm (fun i=>hL (hl i)) (fun i=>hL (ht i)) ih
  | add _ _ ih1 ih2=> exact ih1.add ih2
  | smul a _ ih=> exact ih.smul _
lemma Friends.reserveL (h : Friends L S P) (e : G.ColorIndex) (x:E4) (he : ∀ i∈L,i.1 ≠ x): Friends L (insert x S) P:=by
  induction h with
  | baby=>exact .baby _
  | @joined S P u v h k hm hl ht _ ih=>
    apply Friends.joined u v (by simp [h,show u.1≠x from he _ (hl e)]) (by simp [k,show v.1≠x from he _ (ht e)]) hm hl ht
    unfold Spots at ih ⊢; rw [Finset.insert_comm x u.1,Finset.insert_comm x v.1] at ih; exact ih
  | add _ _ ih1 ih2=>exact ih1.add ih2
  | smul a _ ih=> exact ih.smul _
lemma add_outside (hP : Friends L S P) (e:G.ColorIndex) (x y:Ph) (hx : x.1∉ S∪L.image Prod.fst)
    (hy : y.1∉ S∪L.image Prod.fst) (h:x.1≠y.1) : ∃ L, Friends L S (bilocal G x y*P):=by
  let F (p:Ph):Finset (World G):=Finset.univ.image (cellL p)
  obtain ⟨hx,h1⟩:=(show x.1∉S ∧ ∀ i∈L,i.1≠x.1 from by simpa only [Finset.mem_union,not_or,Finset.mem_image,not_exists,not_and,ne_eq] using hx); obtain ⟨hy,h2⟩:=(show y.1∉S ∧ ∀ i∈L,i.1≠y.1 from by simpa only [Finset.mem_union,not_or,Finset.mem_image,not_exists,not_and,ne_eq] using hy)
  have hf (p:Ph) : covers (F p) p:= fun a=> Finset.mem_image_of_mem (cellL p) (Finset.mem_univ _)
  refine ⟨L ∪ (F x∪ F y),.joined x y hx hy h (fun a=>?_) (fun a=>?_) (((hP.reserveL e _ h2).reserveL e _ h1).extendL (Finset.subset_union_left))⟩
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ (hf x a))
  exact Finset.mem_union_right _ (Finset.mem_union_right _ (hf y a))

lemma cold_in {i j : World G} (h : i.1∈S): (Cold S G).cov i j=(Kf G).cov i j:= by change _ + -(if _ then _ else _)=(Kf G).cov i j; rw [if_pos (Or.inl h),neg_zero,add_zero]
lemma cold_out {i j : World G} (h : i.1∉S) (ht:j.1∉S): (Cold S G).cov i j=0:= by change (Kf G).cov i j + -(if i.1∈ S ∨ j.1∈S then _ else _)=0; simp [h,ht]
lemma rainX (i: World G) (h:i.1∉S) (P : Pol G) (hp : Q∈outer S G) :
    Next.Rank.Normal.blend (Cold S G) 0 (X i*(Q*P))= Next.Rank.Normal.blend (Cold S G) 0 (Q* first (Cold S G) i P) :=by
  rw [stationed]; unfold first; rw [split_leibniz]
  rw [split_eq ((Cold S G).cov i) 0 (fun j hj=> cold_out h hj) (show Q∈supported ℂ {i : World G| i.1∉S} from hp),slit_zero,zero_mul,zero_add]

-- directions. allow arbitrary functions at first.
abbrev Lane (G : Gauge):= G.ColorIndex → World G→ℂ
def fast (S : Finset E4) (x : Ph): Lane G:=fun e=> (Cold S G).cov (cellL x e)

def plow (U V : Lane G) : Module.End ℂ (Pol G):=∑ i, (slit (U i)).toLinearMap ∘ₗ (slit (V i)).toLinearMap
lemma plows (U V : Lane G) (P : Pol G) : plow U V P= ∑ i, slit (U i) (slit (V i) P):= LinearMap.sum_apply ..
lemma plow_swap (U V : Lane G) : plow U V = plow V U:= LinearMap.ext fun p=> by rw [plows,plows]; exact Finset.sum_congr rfl fun i _=> slit_slit ..
lemma plow_fit (U V : Lane G) (h : P∈Lap.scope A): plow U V P∈Lap.scope A:= by rw [plows]; exact Subalgebra.sum_mem _ fun a _=> split_in _ _ (split_in _ _ h)

def permit (S:Finset E4) (Q:Pol G): Pol G→ₗ[ℂ] ℂ:= (Next.Rank.Normal.blend (Cold S G) 0) ∘ₗ LinearMap.mulLeft ℂ Q
lemma plow_out (x y:Ph) (hx:x.1∉ S) (hy:y.1∉ S) (hp : Q∈outer S G) (P : Pol G):
    permit S (bilocal G x y*Q) P = permit S Q (plow (fast S x) (fast S y) P):=by
  have hop (R P : Pol G): permit S R P=Next.Rank.Normal.blend (Cold S G) 0 (R*P):=rfl
  rw [hop,hop,mul_assoc,bilocal,plows]; simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum]
  -- LinearMap.mulLeft unfolded?
  apply Finset.sum_congr rfl; intro i _
  let u:= cellL x i; let v:= cellL y i
  have h : (X u:Pol G)*Q∈outer S G:= Subalgebra.mul_mem _ (X_mem_supported.mpr hx) hp
  rw [show X u * X v*(Q*P)=X v*(X u*Q*P) from by ring, rainX v hy _ h,mul_assoc (X u), rainX u hx _ hp]; rfl

def Rain (S :Finset E4) (A : Finset (World G)): Submodule ℂ (Pol G):= (Lap.scope A).toSubmodule ⊓ ⨅ (i: {R : Pol G//∃ L, Friends L S R}), LinearMap.ker (permit S i.val)
lemma rain_iff : P∈Rain S A ↔ P∈Lap.scope A ∧ ∀ L R, Friends L S R→ permit S R P=0:=by
  simp only [Rain,Submodule.mem_inf,Submodule.mem_iInf, Subalgebra.mem_toSubmodule,LinearMap.mem_ker,Subtype.forall]; simp [forall_comm (α:=Pol G) (β:=Finset (World G))]
lemma silent_rains (e:G.ColorIndex) (h : P∈Lap.scope A) (hp : P∈Room G S) (K : Silent S P): P∈Rain S A:= by
  refine rain_iff.mpr ⟨h,fun L R hL=>?_⟩
  rw [show permit S R P=Next.Rank.Normal.blend (Cold S G) 0 (R*P) from rfl]; exact Frozen e hL hp K
lemma rain_plow (e:G.ColorIndex) (h : P∈Rain S A) (he : Friends L S Q) (x y : Ph)
    (hx : x.1∉ S∪L.image Prod.fst) (hy:y.1∉ S∪L.image Prod.fst) (hk : x.1 ≠ y.1): permit S Q (plow (fast S x) (fast S y) P)=0:=by
  obtain ⟨I,hI⟩:= add_outside he e x y hx hy hk
  rw [← plow_out x y (fun w=> hx (Finset.mem_union_left _ w)) (fun w=> hy (Finset.mem_union_left _ w)) he.outer_fit]; exact (rain_iff.mp h).2 _ _ hI
end YM.XSpace.Legs
