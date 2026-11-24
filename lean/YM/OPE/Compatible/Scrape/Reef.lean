import YM.OPE.Compatible.Scrape.Line
import YM.Next.RANK.LoomNative
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.PathCost
/-!
# A common pallet, for all markers at the declared tuned size
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Next.Rank Next.Rank.Spindle Source Further.CorrectedLift.PathCost
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{E X:Type*}{n:Side}{o:Site n}{b i k r m:ℕ}
local notation "AΛ"=> fieldX (Shade G)
abbrev TilesB (b:ℕ):=UsedEdges (box b)
abbrev DrawerB (G:Gauge)(b:ℕ):=Libra.Keys G (TilesB b)
section
noncomputable def InLine (b:ℕ): fieldX (Shade G) →ₗ[ℝ] DrawerB G b:= LinearMap.pi (fun i=> actualAt i.val)
-- unbundled higher P
noncomputable def stretchB (x:DrawerB G b): AΛ:= fun i=> if h: i.1∈box b ∧ i.1+step i.2.1∈box b then x ⟨(i.1,i.2.1),h⟩ i.2.2 else 0
noncomputable abbrev UnB : DrawerB G b→ₗ[ℝ] fieldX (Shade G):={
     toFun:=stretchB
     map_add' x y:=by funext i; change stretchB (x+y) i=_+_; simp only [stretchB]; split; rfl; simp
     map_smul' t x:=by funext i; change stretchB (t • x) i=t*_; unfold stretchB; split; rfl; simp }
lemma ambry (x:DrawerB G b): InLine b (UnB x)=x:=by ext1 i; ext1 j; change stretchB x (i.val.1,i.val.2,j)=_; unfold stretchB; rw [dif_pos i.property]
noncomputable abbrev crevy (u : G.El) : DrawerB G b→L[ℝ] DrawerB G b:=ContinuousLinearMap.pi fun i=> (G.adjoint u).toContinuousLinearMap ∘L (ContinuousLinearMap.proj i)
noncomputable def liftP (b:ℕ): fieldX (Shade G) →ₗ[ℝ] DrawerB G b:= LinearMap.pi (fun i=> royal i.val)
lemma voles (h:b≤r) (x:TilesB b) : x.val.1∈box r∧x.val.1+step x.val.2 ∈box r:= ⟨borrow _ _ h x.property.1,borrow _ _ h x.property.2⟩
lemma Vibe (x:Cover) (hx:x∈box b): (carryP x).length ≤ 4*b:=by rw [carryP, Stationary.route_length, sub_zero]; exact Spindle.bounded hx
lemma Tumb (x:Cover)(hx:x∈box b)(y) (hy:y∈ visits 0 (carryP x)): y∈box (4*b):=borrow _ _ (by have h:=Vibe x hx; omega) (passages 0 (carryP x) (by simp) y hy)
lemma blueprint (x y:AΛ)(h: InLine b x =InLine b y)(p:Cover)(w:Walk)(hz:∀ z∈visits p w,z∈box b):sprig p w x=sprig p w y:=by
     change (pieces _ _ _).sum=(pieces _ _ _).sum; induction w generalizing p with
     | nil=>rfl
     | cons i w ih=>
          have he(z)(hj:z∈ visits (p+i.vec) w):=hz z (List.mem_cons_of_mem _ hj); have hy: p+i.vec∈ box b:= he _ (by cases w <;> simp [visits]); let u:=i.used p; have hv:u.1∈box b∧ u.1+step u.2∈ box b:=by
             have hx:= hz _ (show p∈visits p (i::w) from List.mem_cons_self); unfold u; cases i with| mk i v=> cases v <;> simp_all [Step.used,Step.vec,sub_eq_add_neg]
          let j:TilesB b:=⟨u,hv⟩; rw [pieces,List.sum_cons,pieces,List.sum_cons,ih (p+i.vec) he,show indexS u x=indexS u y from congr_fun h j] -- unfolding
lemma reelB {x y:AΛ}(h:InLine (4*b) x=InLine (4*b) y):liftP b x=liftP b y:=by
      funext i; let j:TilesB (4*b):= ⟨i.val,voles (by omega) i⟩; change indexS i.val x+_ -_=indexS _ y+_-_; rw [show indexS i.val x=indexS i.val y from congr_fun h j]; rw [blueprint _ _ h 0 (carryP i.val.1) (Tumb _ i.property.1)]; rw [blueprint _ _ h 0 (carryP _) (Tumb _ i.property.2)]
noncomputable def socket (b:ℕ) : DrawerB G (4*b)→L[ℝ] DrawerB G b:= (liftP b ∘ₗ UnB).toContinuousLinearMap
lemma homeB (b:ℕ)(x:AΛ): socket b (InLine (4*b) x)=liftP b x:=reelB (ambry (InLine (4*b) x))
lemma loopletB (b:ℕ)(u:G.El)(x:AΛ): InLine b (plumeX u x)= crevy u (InLine b x):=rfl
lemma wharfB (b:ℕ)(x:AΛ)(u:G.El): liftP b (plumeX u x)= crevy u (liftP b x):= funext fun i=> ShamRock i.val x u
lemma chive (x:DrawerB G (4*b))(u:G.El): socket b (crevy u x)= crevy u (socket b x):=by
      let q:=UnB x; have hx:InLine (4*b) q=x:=ambry x; rw[← hx,← loopletB, homeB, wharfB,homeB]
lemma blown (b:ℕ)(x:fieldX G.ColorIndex):socket b (InLine (4*b) (mountain x))=0:=by rw[homeB]; exact funext fun i=> sham _ _
lemma chordBudget (x: DrawerB G b)(i:Edge Cover) : ‖indexS i (UnB x)‖≤ ‖x‖:=by
     by_cases hj : i.1∈box b∧i.1+step i.2∈box b
     · let v:TilesB b:=⟨i,hj⟩; rw [show indexS i (UnB x)=x v from congr_fun (ambry x) v]; exact norm_le_pi_norm x v
     rw [show ‖indexS i (UnB x)‖=0 from ?_]; exact norm_nonneg x; apply norm_eq_zero.mpr; ext1 j; change stretchB x _=_; unfold stretchB; exact dif_neg hj
lemma pathsGain (x:AΛ){C:ℝ}(h:∀ i:Edge Cover,‖indexS i x‖≤C) (p:Cover)(w:Walk): ‖sprig p w x‖ ≤ C*w.length:=by
     change ‖(pieces _ _ _).sum‖ ≤ _; induction w generalizing p with
     | nil=> simp [pieces]
     | cons a w ih=> rw [pieces,List.sum_cons]; refine (norm_add_le ..).trans ((add_le_add (b:=C) ?_ (ih (p+a.vec))).trans_eq ?_); split; rw [norm_neg]; exact h _; exact h _; rw [List.length_cons,Nat.cast_add,Nat.cast_one];ring
lemma RootNorm (b:ℕ): ‖(socket b:DrawerB G _→L[ℝ] DrawerB G _)‖≤1+8*(b:ℝ):=by
     apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro x; apply pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))|>.mpr; intro i; let u:=UnB x; have ht (p:Cover) (hx:p∈box b): ‖sprig 0 (carryP p) u‖ ≤ ‖x‖*(4*b):= (pathsGain u (chordBudget x) 0 _).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Vibe p hx) (norm_nonneg _)); exact (norm_sub_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (chordBudget x i.val) (ht _ i.property.1))) (ht _ i.property.2)).trans_eq (by ring))
end
end YM.OPE.Spells
