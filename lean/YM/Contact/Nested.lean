import YM.Contact.PlantBundle

/-!
# Finer chessboard estimate inside the entire replicated product

This does NOT propagate its composite insertion through Wilson steps on its own.
Instead it gives a coarse centered-cell root estimate by running one fine chessboard
on the actual packed arrays, given separate prices at the still distinct fine sites.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Nested
open Function Filter Set Lattice Wilson RG Cells Extraction Push Push.RelayDifference MeasureTheory
open scoped BigOperators Topology Classical
open YM.MergeProof.Ribbons
variable {G:Gauge}{C:Family G}{p N J m k:ℕ}{I:Type*}[Fintype I]

lemma center_affine (h:m≤N) (v:(center C.S p h 0).Cell) (y:Site (C.S.side N p)) :
    (center C.S p h 0).copyMap v y=((center C.S p h 0).omega v).act y+(C.S.toDepth h p).embed v:=by
    let X:=center C.S p h 0
    have he:X.copyMap v 0=(C.S.toDepth h p).embed v:=by
       change (center C.S p h 0).copyMap v 0=_
       rw [Cells.copy_home,zero_add]
    change (X.omega v).act y+X.translateBy v= (X.omega v).act y+_
    have ht: X.translateBy v= _ := (show X.copyMap v 0 = X.translateBy v from by simp [Tiling.copyMap, Lattice.affine]) ▸ he
    rw [ht]

omit [Fintype I] in
lemma nested_separation (hm:m≤N) (x:I→Site (C.S.side N p))(l:ℕ)
    (hx:∀ i i',pdist (x i) + pdist (x i') + l < Cells.span C.S hm p)(ht:∀ i j:I,i≠j→l<separation (x i) (x j))
    (i j:(center C.S p hm 0).Cell × I) (hij:i≠ j): l < separation ((center C.S p hm 0).copyMap i.1 (x i.2)) ((center C.S p hm 0).copyMap j.1 (x j.2)) := by
      let T:=center C.S p hm 0
      rw [center_affine hm,center_affine hm]; let d:=C.S.toDepth hm p
      change l < separation ((T.omega i.1).act _ + d.embed i.1) ((T.omega j.1).act _ + d.embed j.1)
      by_cases he:i.fst=j.fst
      · rw [he,separation_translate,separation_signed]; exact ht i.2 j.2 fun q=>hij (Prod.ext he q)
      let a:= (T.omega i.1).act (x i.2); let b:= (T.omega j.1).act (x j.2)
      let A:= d.embed i.1; let B:=d.embed j.1
      have ha:= separation_triangle A (a+A) (b+B); have hb:= separation_triangle A (b+B) B
      have hcount: Cells.span C.S hm p≤ separation A B:=by rw [Next.Rank.Station.both]; exact Nat.le_mul_of_pos_right _ (Next.Rank.Station.separation_pos _ _ he)
      have e1: separation A (a+A)=pdist (x i.2):=by rw [separation_comm]; simp [a,separation];
      rw [e1] at ha
      have e2: separation (b+B) B=pdist (x j.2):=by simp [b,separation]
      rw [e2] at hb
      have := hx i.2 j.2
      change l < separation (a+A) (b+B)
      omega

lemma coarser_affine (hm:m≤J)(hf:J≤N) (s:Signed)(v:Site (C.S.side m p))(x:Site (C.S.side N p)):
     s.act x + (C.S.toDepth (hm.trans hf) p).embed v=s.act x + (C.S.toDepth hf p).embed ((C.S.toDepth hm p).embed v):= by
        congr 1
        exact Next.Rank.Station.embed_comp (C.S.toDepth hm p) _ _ _

variable (hm:m≤J)(hk:J≤k)(hN:k≤N)

lemma clearance_fine (x:I→Site (C.side N p))
     (hx:∀ i i',pdist (x i)+pdist (x i') + Cells.span C.S (hk.trans hN) p < Cells.span C.S (hm.trans (hk.trans hN)) p)
     (ht:∀ i j:I,i≠j→Cells.span C.S (hk.trans hN) p < separation (x i) (x j))
     (F:Tiling (C.side N p))(hF:F.side.val=Cells.span C.S (hk.trans hN) p)
       (i j:(center C.S p (hm.trans (hk.trans hN)) 0).Cell × I):
   let u := (center C.S p (hm.trans (hk.trans hN)) 0).copyMap i.1 (x i.2)
   let v := (center C.S p (hm.trans (hk.trans hN)) 0).copyMap j.1 (x j.2)
   u ∈ F.chamber (F.which u) → v ∈ F.chamber (F.which v) → F.which u = F.which v → i = j :=by
     intro u v hu hv he; by_contra! hne
     rw [←he] at hv
     exact lt_irrefl (a:=separation u v) ((F.extent hu hv).trans_eq hF|>.trans_lt (nested_separation (hm.trans (hk.trans hN)) x _ hx ht _ _ hne))

-- actual cache usage hN equality
lemma coarser_plantable (x:I→Site (C.side N p))
     (hf:Fintype.card (Signed × I)*(2*(3*Cells.span C.S hN p+Cells.span C.S hN p+1)) < Cells.span C.S (hk.trans hN) p):
   let X:= (center C.S p (hm.trans (hk.trans hN)) 0)
   ∃ F:Tiling (C.side N p), F.side.val=Cells.span C.S (hk.trans hN) p ∧ ∀ i:X.Cell × I,
       (X.copyMap i.1 (x i.2)) ∈ F.margin (F.which (X.copyMap i.1 (x i.2))) (3*Cells.span C.S hN p) :=by
   classical
   intro X
   let e:= Fintype.equivFin (Signed × I)
   let ζ(i:X.Cell × I):=e (X.omega i.1,i.2)
   let q(i:Fin (Fintype.card (Signed × I))):=(e.symm i).1.act (x (e.symm i).2)
   let p'(i:X.Cell × I):Site (C.side J p):=(C.S.toDepth hm p).embed i.1
   exact place_together hN hk hf le_rfl ζ q p' (fun _ => 0) (fun i=>by simp only [q,ζ,e.symm_apply_apply,map_zero,add_zero]; exact (center_affine _ _ _).trans (coarser_affine hm (hk.trans hN) _ _ _)) (fun i l=>by simp)


def clusterAt (x:I→Site (C.side N p))(O:I → Config G (C.side N p)→ℂ) : Config G (C.side N p)→ℂ:= fun z=> ∏ i, RelayDifference.oriented (O i) false 1 (x i) z
lemma copy_product {n:Side}(F:Tiling n)(i:F.Cell)(T:I→ Config G n→ℂ): (F.copy (G:=G) i fun z=>∏ j,T j z)=(fun z=>∏ j,F.copy i (T j) z):=by
     funext z; unfold Tiling.copy; split_ifs <;> simp_all only [star_prod]
lemma inner_array (x:I→Site (C.side N p))(O:I → Config G (C.side N p)→ℂ)(X:Tiling (C.side N p))(z:Config G (C.side N p)):
   let y(i:X.Cell × I):Site (C.side N p):=X.copyMap i.1 (x i.2)
   let key(i:X.Cell × I):= RelayDifference.oriented (O i.2) ((decide (X.hand i.1)).xor false) (X.omega i.1 * 1) (y i) z
   ∏ i:X.Cell, X.copy i (clusterAt x O) z = ∏ i:X.Cell × I,key i:=by
     classical
     intro y key
     rw [←Finset.univ_product_univ,Finset.prod_product]
     congr 1; funext j -- maybe finset?
     unfold clusterAt; rw [copy_product]; apply Finset.prod_congr rfl; intro i hi
     dsimp only [key,y]; rw [copied]
lemma repeated_price {n:Side}(X:Tiling n)(u:I→ℝ): ∏ i:X.Cell × I, u i.2=(∏ i,u i)^Fintype.card X.Cell := by simp [← Finset.univ_product_univ,Finset.prod_product]
lemma coarser_product (hh:C.Makes) (x:I→Site (C.side N p))(O:I → Config G (C.side N p)→ℂ)(fees:I→ℝ)
     (hx:∀ i i',pdist (x i)+pdist (x i') + Cells.span C.S (hk.trans hN) p < Cells.span C.S (hm.trans (hk.trans hN)) p)
     (ht:∀ i j:I,i≠j→Cells.span C.S (hk.trans hN) p < separation (x i) (x j))
     (hf:Fintype.card (Signed × I)*(2*(3*Cells.span C.S hN p+Cells.span C.S hN p+1)) < Cells.span C.S (hk.trans hN) p)
     (hp:∀ i,BlockCost (Q:=C.S) (p:=p) (N:=N) (O i) k (C.beta N p) (fees i)) :
   let X:= (center C.S p (hm.trans (hk.trans hN)) 0)
   X.rootTest (C.beta N p) (clusterAt x O) ≤ ∏ i,fees i :=by
   classical
   intro X
   let y(i:X.Cell × I):=X.copyMap i.1 (x i.2); let tw(i:X.Cell × I):=(decide (X.hand i.1)).xor false; let tg(i:X.Cell × I):=X.omega i.1 * 1
   have hz : ‖moment (C.beta N p) (fun z=>∏ i:X.Cell × I, RelayDifference.oriented (O i.2) (tw i) (tg i) (y i) z)‖ ≤ ∏ i:X.Cell × I,fees i.2 := plant_typed (fun (i:X.Cell × I)=> O i.2) y tw tg (fun i=> fees i.2) (fun i=>hp i.2) (by intro i; unfold tg; rw [mul_one]; exact (rfl : diag (X.omega i.1))) hN hk (Cells.seamless hh N p) (fun F he hv i j hij=>clearance_fine hm hk hN x hx ht F he i j (hv i) (hv j) hij) (coarser_plantable hm hk hN x hf)
   have hE := repeated_price X fees
   simp_rw [← show ∀ z:Config G (C.side N p), ∏ i:X.Cell, X.copy i (clusterAt x O) z = ∏ i:X.Cell × I, RelayDifference.oriented (O i.2) (tw i) (tg i) (y i) z from fun z=>inner_array x O X z,hE] at hz
   apply le_of_pow_le_pow_left₀ (n:=Fintype.card X.Cell) (by simp) -- investigate signature
   · exact Finset.prod_nonneg (fun i _=>(hp i).positive)
   exact (X.powering _ _).trans_le hz
end YM.Contacts.Nested
