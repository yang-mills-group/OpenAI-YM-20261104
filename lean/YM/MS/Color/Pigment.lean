import YM.MS.Color.Commutation
/-!
# Color rotation stays in local-polynomial subspaces. Use full H later.

Suffices with conjugation as separate after mean. Need Plane.Solid operations too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Color
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule
open Local Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G : Gauge} {P D : Type}
    {g : Twig (Branch G D) P} {F:Score G D P}
variable (k:G.El)
-- one letter color

def advance (k:G.El) : (Twig (Branch G D) P)→ₗ[ℂ] (Twig (Branch G D) P) where
   toFun f i:= ∑ c: CI G, wc k i.1.2 c * f (setLeg i c)
   map_add' f g:= by ext; simp [mul_add, Finset.sum_add_distrib]
   map_smul' c f:= by ext; simp [mul_left_comm c, Finset.mul_sum]
lemma advance_bud : repeatC k (bud g F)=bud (advance k g) (repeatC k F):= by
    ext l; cases l with
    | nil=> simp
    | cons i w=> have hv i:Koszul.D i (bud g F) = g i • F:=rfl
                 rw [repeat_cons,bud_cons]; simp_rw [show ∀ i,Koszul.D i (bud g F)=g i • F from hv,map_smul]; simp [advance, Finset.sum_mul,mul_assoc]
lemma advance_nil : repeatC (P:=P) (D:=D) k hit=hit:=by
    ext l; cases l with
    | nil=> simp
    | cons i w=> have he (j): Koszul.D j (hit (A:= Leg D G.ColorIndex) (P:=P))=0:=rfl
                 simp [repeat_cons,he]
variable {r : ℕ}
lemma adv_line (u: Fin r→Twig (Branch G D) P) : repeatC k (Local.line r u)=Local.line r (fun i=> advance k (u i)):= by
   induction r with
   | zero=> exact advance_nil k
   | succ r ih=> rw [line_bud,line_bud,advance_bud,ih]; rfl

open Local.BV.Woven Local.BV
variable {h q:ℤ} {f:Grade G} {u r:ℕ}
lemma stays (H:f∈ yields h q): advance k f∈yields h q:= by
   refine seedStar.mpr ⟨fun i=>?_,fun i hi=> ?_⟩
   · let V j: FourP → ℂ:= fun q=> f ((i.1,j),q)
     have ht j: Plane.Shape (V j) (h-mslug i):= (seedStar.mp H).form (i.1,j)
     convert (Plane.Shape.sum (s:=Finset.univ) (fun j _=> (ht j).scalar (wc k i.2 j))) using 1; ext; rw [Finset.sum_apply]; rfl
   change ∑ j:CI G,_=0; exact Finset.sum_eq_zero fun j _=> mul_eq_zero_of_right _ ((seedStar.mp H).real' (setLeg i j) hi)
lemma stable {f:Grade G}: Q (advance k f)=advance k (Q f):=by
    suffices he: bud (advance k (Q f)) hit=bud (Q (advance k f)) hit by
       ext x; simpa only [bud_cons,hit_nil,mul_one] using congr_fun he.symm [x]
    have he (f : Grade G): natQ (bud f hit)=bud (Q f) hit:= by
       ext l; change Gof.Q (bud f hit) l= _; cases l with
       | nil=> simp
       | cons i l=> rw [MatrixLet.acts,MatrixLet.no]; simp
    have hv : repeatC k (natQ (bud f hit))= natQ (repeatC k (bud f hit)):= commute k _
    rwa [he,advance_bud,advance_bud,advance_nil,he] at hv
lemma repeat_bed {F : Law G} (hF:F∈Bed G h q r): repeatC k F∈Bed G h q r:= by
   suffices he : Bed G h q r ≤ Submodule.comap (repeatC k) (Bed G h q r) from he hF
   apply bed_le; rintro f x y hx rfl rfl hn; rw [Submodule.mem_comap,adv_line]; exact tileCub.mpr (line_in mslug ghostNo (fun i=> seedStar.mp (stays k (hx i))))
lemma repeat_carry {F : Law G} (hF:F∈Carry G h r): repeatC k F∈ Carry G h r:=by
   suffices he : Carry G h r ≤ Submodule.comap (repeatC k) (Carry G h r) from he hF
   rw [Carry,span_le]; rintro F ⟨p,w,H,rfl,rfl⟩; rw [SetLike.mem_coe,Submodule.mem_comap,adv_line]
   exact subset_span (mem_setOf.mpr ⟨_,w,fun i=> And.intro (stays k (H i).1) (by rw [stable, (H i).2,map_zero]),rfl,rfl⟩)
end YM.MS.Color
