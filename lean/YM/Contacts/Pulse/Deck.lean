import YM.Contacts.Pulse.Bind
import YM.Contacts.Pulse.Rebase
import YM.Next.FREE_KERNELS.Bank
namespace YM.Pulse.Spine
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free
open scoped Classical Topology BigOperators NNReal ENNReal
noncomputable section
variable {α β X Y Z E ι: Type} {L c f n : Side}
def lower (n:Side) (p: Node α) : Co n α:=(wrap n p.1,p.2)
lemma lower_onto (n:Side): Surjective (lower (α:=α) n):= fun ⟨x,a⟩=> ⟨(lift x,a),Prod.ext (wrap_lift _) rfl⟩
def plane (R:Row α β) (x:Node α)(y:Node β) := R x.2 y.2 (y.1-x.1)
def both (G:X→X→ℝ) (x:Fin 2→X):ℝ:= G (x 0) (x 1)
lemma incl_up (R:Row α β)(n:Side)(x:Node α)(y:Co n β) : R.acts n (lower n x) y= MergeProof.cram (lower n) (plane R x) y:= by
  let k:= fun z:Cover => if y.1=wrap n x.1 + wrap n z then R x.2 y.2 z else 0; rw [expand_eq]
  let g (z:Cover) : Node β:= (x.1+z,y.2); have hg : Injective g:= fun a b h=> add_left_cancel (congr_arg Prod.fst h)
  let w (i:Node β):= if lower n i=y then plane R x i else 0
  have hh : Function.support w ⊆ Set.range g := fun i hi=> by
    have hz : lower n i=y := by by_contra e; exact hi (if_neg e)
    exact ⟨i.1-x.1,Prod.ext (by exact add_sub_cancel ..) (show y.2=i.2 from congr_arg (fun z:Co n β=> z.2) hz.symm)⟩
  change tsum k = tsum w; apply Eq.trans ?_ (hg.tsum_eq hh); apply tsum_congr; intro z; rcases y with ⟨p,b⟩; simp [g,k,w,plane,Function.comp_apply,lower,eq_comm]
lemma nsmul_rent (n:Side)(z x:Cover): rent n (x+n.val • z)=rent n x+z:= Eq.symm (rent_unique (by
  have hu := rent_balance n x; suffices h:x+ n.val • z = lift (wrap n x) + n.val • (rent n x+z) by rw [(rent_raw _ _ _ h).1]; exact h
  rw [smul_add,←add_assoc,←hu]))
lemma wrap_slot (n:Side)(x:Node α)(z:Cover): lower n (backpack (n.val • z) x)= lower n x:= Prod.ext ((rent_raw _ _ (wrap n x.1) (show x.1+n.val • z=lift (wrap n x.1)+ n.val • (rent n x.1 + z) by rw [smul_add,←add_assoc,←rent_balance])).1) rfl
lemma lower_eq (n:Side) (x y:Node α)(h: lower n x=lower n y): backpack (n.val • (rent n y.1-rent n x.1)) x=y := Prod.ext (by
  change x.1+n.val • (rent n y.1-rent n x.1) = y.1; conv_rhs=> rw [rent_balance n y.1]
  conv_lhs=> lhs; rw [rent_balance n x.1,show wrap n x.1=wrap n y.1 from congr_arg Prod.fst h]
  rw [smul_sub]; abel) (congr_arg (fun z : Co n α=> z.2) h)

-- use explicit equivalence of fibers for all stages, no proof branching
variable (n)
def berth (x:Node α): Cover ≃ {z:Node α// lower n z=lower n x} := ⟨fun v=>⟨backpack (n.val • v) x,wrap_slot n x v⟩,fun z=>rent n z.1.1-rent n x.1,
    fun y=>by change rent n (x.1+n.val • y)-rent n x.1=y; rw [nsmul_rent,add_sub_cancel_left], fun z=>Subtype.ext (lower_eq n x _ z.2.symm)⟩
lemma cram_board (u:Node α→ℝ)(x:Node α): MergeProof.cram (lower n) u (lower n x)=∑' i:Cover,u (backpack (n.val • i) x):= ((berth n x).tsum_eq _).symm
variable {n} {R:Row α β}
lemma trails_iff {K:Node α→Node β→ℝ}{R:Co c α→ Co f β→ℝ}(h:∀ x y z,K (backpack (c.val • z) x) (backpack (f.val • z) y)=K x y)(he:∀ x,Scroll (lower f) (K x) (R (lower c x))): Trails (lower c) (lower f) K R:= by
  refine ⟨he,fun y p=>?_⟩; obtain ⟨x,rfl⟩:= lower_onto c p
  rw [flip,he,cram_board,cram_board,← (Equiv.neg Cover).tsum_eq]; apply tsum_congr; intro z; symm; change K _ y = _
  rw [← h x _ z]; congr 1; refine Prod.ext ?_ rfl -- maybe
  symm; change y.1+ f.val • (-z)+f.val • z = y.1; rw [smul_neg]; abel
lemma row_ship (R:Row α β)(n:Side) : Trails (lower n) (lower n) (plane R) (R.acts n):= trails_iff (fun x y z=> by simp [backpack,plane]) (fun y=> incl_up R n y)
lemma cell_stamp (g:Ratio c f) (x:Cover): g.parent (wrap f x)=wrap c (rent g.count x):= by
  have hh : wrap f x=g.assemble (wrap c (rent g.count x),wrap g.count x) := by
    conv_lhs => rw [rent_balance g.count x]
    rw [Ratio.assemble,map_add,g.embed_wrap,add_comm]
  rw [hh,g.assemble_parent]
lemma plot_inertia (R: Cross L α β)(x y)(z:Cover) : install R (backpack (L.val • z) x) (backpack z y)=install R x y:= by
  simp only [install,backpack,Equiv.prodCongr_apply,Equiv.coe_addRight,Equiv.refl_apply,Prod.map]; rw [nsmul_rent,add_sub_add_right_eq_sub]; rw [show wrap L (x.1+L.val • z)=wrap L x.1 from congr_arg Prod.fst (wrap_slot L x z)]
lemma st_new (g:Ratio c f) (R:Cross g.count α β): Trails (lower f) (lower c) (install R) (installed g R):= by
  apply trails_iff (fun x y z=> by rw [g.exact_size,mul_comm, mul_smul]; apply plot_inertia)
  intro x y; let a:= wrap g.count x.1; let p:Node (Co g.count α):=(rent g.count x.1,a,x.2); unfold installed; rw [Matrix.submatrix_apply,split_co]; change Row.acts R _ (g.parent (wrap f x.1),g.residue (wrap f x.1),x.2) y=_; rw [cell_stamp,g.residue_wrap]; exact incl_up R c p y
def band (X:Type) (i:Fin 2)(x:X) : Locked X i x≃ X := (prelude (n:=1) X i x).trans (Equiv.funUnique (Fin 1) X)
lemma band_step (p:X→Y) (i:Fin 2)(x:X) (u:Locked X i x): band Y i (p x) (roll p i x u)=p (band X i x u):= rfl
lemma band_zero (x:X)(u:Locked X (0:Fin 2) x): band X 0 x u=u.val 1:= rfl
lemma band_one (x:X)(u:Locked X (1:Fin 2) x): band X 1 x u=u.val 0:= rfl
lemma title {p:X→Y}{G:X→X→ℝ}{H:Y→Y→ℝ}(h:Trails p p G H): Shadow p (both G) (both H):= by
  intro i x; let y:=p x; fin_cases i
  · change Scroll (roll p (0:Fin 2) x) _ _; convert (h.row x).across (band X 0 x) (band Y 0 (p x)) (band_step p 0 x) using 1 <;> ext z <;> simp only [both,Function.comp_apply,band_zero,(show z.val 0=_ from z.property)]
  change Scroll (roll p (1:Fin 2) x) _ _; convert (h.col x).across (band X 1 x) (band Y 1 (p x)) (band_step p 1 x) using 1 <;> ext z <;> simp only [both,Function.comp_apply,flip,band_one,(show z.val 1=_ from z.property)]
-- allAt finite rank2 formula
lemma fasten [Fintype X] (G K:X→Y→ℝ)(F:X→X→ℝ) (y:Fin 2→Y): allAt ![G,K] (both F) y= ((of G)ᵀ* of F * of K) (y 0) (y 1):= by
  let e : X×X≃(Fin 2→X):= (Equiv.prodCongr (Equiv.refl X) (Equiv.funUnique (Fin 1) X).symm).trans (Fin.consEquiv (n:=1) (fun _ =>X))
  unfold allAt; rw [tsum_fintype,← Equiv.sum_comp e,Fintype.sum_prod_type,Matrix.mul_apply]
  simp_rw [Matrix.mul_apply,sum_mul,Matrix.transpose_apply, of_apply]
  rw [sum_comm]; apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _; rw [Fin.prod_univ_two]; change F b a * (G b (y 0)*K a (y 1))=_; ring

variable [Fintype ι]{F:YM.Pulse.Field ι (Node α)}{m:ℕ→Side}{k:∀ j, YM.Pulse.Field ι (Co (m j) α)}
    {l:Range (Node α)}{d:ℝ}
lemma lower_separates (hm:Tendsto (fun j=>(m j).val) atTop atTop) (x y:Node α) : ∀ᶠ j in atTop, lower (m j) x=lower (m j) y→x=y := by
  filter_upwards [eventually_unfold m hm x.1,eventually_unfold m hm y.1] with j hx hy h; exact Prod.ext (hx ▸ hy ▸ congr_arg lift (show wrap (m j) x.1=wrap (m j) y.1 from congr_arg Prod.fst h)) (congr_arg (fun z:Co (m j) α=> z.2) h)
lemma arrive (hm:Tendsto (fun j=>(m j).val) atTop atTop) (h:Rooted l F d)(hp:∀ j,Shadow (lower (m j)) F (k j)) (x : ι→Node α)(i:ι) : Tendsto (fun j=> k j (lower (m j)∘x)) atTop (𝓝 (F x)) := by
  let v: Locked (Node α) i (x i):= ⟨x,rfl⟩; let u j := roll (lower (m j)) i (x i); let f (j:ℕ)(w : Locked (Node α) i (x i)):= if u j w=u j v then F w.val else 0
  let g (w: Locked (Node α) i (x i)):= if w=v then F w.val else 0
  have he j : k j (lower (m j) ∘ x)=∑' w,f j w:= (hp j i (x i) (u j v)).trans (expand_eq ..)
  have hl (w): Tendsto (fun j=> f j w) atTop (𝓝 (g w)):= by
    apply Filter.EventuallyEq.tendsto
    filter_upwards [eventually_all.mpr (fun k:ι=> lower_separates hm (w.val k) (x k))] with j hj; unfold f g; by_cases h:w=v; · rw [h]; simp
    rw [if_neg ?_,if_neg h]; intro he; exact h (Subtype.ext (funext fun k=> hj k (congr_fun (congr_arg Subtype.val he) k)))
  simp_rw [he]; have hx:= tendsto_tsum_of_dominated_convergence (h.raw ..).2.1 hl (Eventually.of_forall fun i w=> show ‖f i w‖ ≤ ‖F w.val‖ from by unfold f; split_ifs <;> simp); simpa only [g,v,tsum_ite_eq] using hx
lemma shadow_compare {t:Range (Node α)}{G:YM.Pulse.Field ι (Node α)}{c:ℝ}[Nonempty ι] (hm:Tendsto (fun j=>(m j).val) atTop atTop) (h:Rooted l F d) (hs:Rooted t G c) (hk:∀ j,Shadow (lower (m j)) F (k j) ∧ Shadow (lower (m j)) G (k j)): F=G := funext fun x=> tendsto_nhds_unique (arrive hm h (fun j=>(hk j).1) x (Classical.arbitrary ι)) (arrive hm hs (fun j=>(hk j).2) x (Classical.arbitrary ι))
end
end YM.Pulse.Spine
