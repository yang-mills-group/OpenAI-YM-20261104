import YM.OPE.Compatible.Nectar.Lathe
/-! # Finite section -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp
open scoped Topology BigOperators Classical
variable {r d m n z:ℕ}{c:ℝ}{V I W:Type*}{G:Gauge}
namespace Script
open Page
def pulp (G:Gauge)(d:ℕ):fieldX (Shade G) →ₗ[ℝ] Alphabet G d:= LinearMap.pi (fun x:Fin d=> templateX G x.val)
abbrev car (A:Chord G d r):= A.compLinearMap (fun _=>pulp G d)
lemma plumRealm (G:Gauge)(d:ℕ):Realm (pulp G d):= realms (I:=Fin d) (X:=pulp G d) (f:=fun j:Fin d=>fun x:Alphabet G d=> x j) fun _=> realmBase
lemma crystal (A:Chord G d r):∃ p:Script (Shade G) r, Brief p ∧ wholeX p=car A:=by
    obtain ⟨s,h⟩:= plumRealm G d; exact script_forms _ s (fun v w H=>congr_arg A (funext fun i=> h (v i) (w i) (H i)))
variable {p: Script (Shade G) r}
lemma grammar (A:partX G r n d) (hp: soot m p c)(h:wholeX p= car A.val): p.sorted ∧ p.abides ∧ p.painted:=by
    have Hp:= (show Off G r n d A.val from A.property); have hk:=sootS hp
    refine ⟨fun j=> ?_,fun i n w u=>?_,fun n u x=>?_⟩
    · let f:=epochX; have hv: Tendsto (fun i=>(f i).val) atTop atTop:= tendsto_add_atTop_nat 1; have he := swing_sum p hk j
      ext1 i
      refine tendsto_nhds_unique_of_eventuallyEq (lands _ he i f hv) (lands p hk i f hv) (Eventually.of_forall fun v=> ?_)
      dsimp only; rw [rotating,bridgeX,bridgeX,h]; let N(j):=unfoldX (hand i (f v) j); exact Hp.Perms (fun k=> pulp G d (N k)) j
    · rw [bridgeX,h]; apply MultilinearMap.map_coord_zero (f:=A.val) (i:=i)
      dsimp only; rw [Function.update_self]; ext1 j; have hu: unfoldX (cliff u)=mountain fun p=>(u (wrap _ p.1,p.2)):=by ext t; simp [unfoldX,cliff,mountain]
      rw [hu]; exact temp_zero _
    rw [bridgeX,bridgeX,h]; let v i:= unfoldX (u i); change A.val (fun i=> pulp _ d (plumeX x (v i)))=A.val _; rw [show (fun i=>pulp G d (plumeX x (v i)))=(fun i=> spray x (pulp G d (v i))) from funext fun j=>funext fun i=>color_template ..]; exact Hp.Colors ..
lemma grade_silent (A:partX G r n d) (x: Fin r→fieldX (Shade G)){k:Fin r→ℕ}(hp:∀ i,Low (x i) (k i)) (hg:∑ i,k i< n): car A.val x=0:=by
    let z(i): Alphabet G d:= pulp G d (x i); change A.val z=0; rw [deckSum]; apply sum_eq_zero; intro i _; by_cases he:rankX i=n; swap
    · exact (show Off G r n d A.val from A.property).Grades _ _ he
    obtain ⟨j,hj⟩:=not_forall.mp (show ¬ ∀ j:Fin r,(i j).val+1≤k j from fun u=> not_le_of_gt hg ((sum_le_sum fun j _=> u j) |>.trans' he.symm.le))
    have h: z j (i j)=0:= retainedX _ (hp j) (by omega); exact A.val.map_coord_zero j (show monoX (i j) (z j (i j))=0 by rw [h];simp [monoX])
lemma grade_equal (A:partX G r n d)(k:Fin r→ Fin d)(v:∀ j: Fin r,Taylor G (k j).val) (hh:rankX k=n): car A.val (fun j=> ledge (v j).val)=A.val (fun j=> monoX (k j) (v j)):=by
   let z j:= pulp G d (ledge (v j).val); change A.val z=_; rw [deckSum, sum_eq_single k]; swap
   · intro i _ hi; by_cases h:rankX i=n; swap; · exact (show Off G r n d A.val from A.property).Grades _ _ h
     obtain ⟨j,hj⟩:=not_forall.mp (show ¬ ∀ j:Fin r,i j ≤ k j from fun u=>by
        obtain ⟨j,hj⟩:=not_forall.mp (show ¬ ∀ j,i j=k j from fun t=>hi (funext t)); have hp:rankX i<rankX k:= sum_lt_sum (fun i _=>Nat.add_le_add_right (u i) _) ⟨j,mem_univ _,Nat.add_lt_add_right (lt_of_le_of_ne (u j) (fun g=>hj (Fin.ext g))) _⟩; rw [h,hh] at hp; exact lt_irrefl _ hp)
     have hz:z j (i j)=0:= retainedX _ (ledgeL (v j).val) (Nat.add_lt_add_right (lt_of_not_ge hj) _); exact A.val.map_coord_zero j (show monoX (i j) (z j (i j))=0 by rw [hz]; simp [monoX])
   · apply congr_arg; ext1 i; rw [show z i (k i)=v i from decisions ..]
   simp
lemma graded_horizon (A:partX G r n d) (hp:soot m p c)(hz:n≤m)(h:wholeX p=car A.val): p.Bells n:=by
   have Hv(z:ℕ)(hg:z≤n): p.Bells z:=by
      induction z with
      | zero=> exact fun _ _ hi=>False.elim (Nat.not_lt_zero _ hi)
      | succ v ih=>
         apply chimes hp (grammar A hp h).2.1 (ih (Nat.le_trans (Nat.le_succ _) hg)) (by omega); intro y hP u; rw [h]; exact grade_silent A _ (fun i=> ledgeL (u i).val) (Nat.lt_of_lt_of_le (hP.trans_lt (Nat.lt_succ_self _)) hg)
   exact Hv _ le_rfl
lemma earns (A:partX G r n d) (hp:soot m p c) (hx:n≤ m)(h:wholeX p=car A.val): honeyX p hp hx d=A.val:=by
    obtain ⟨hs,-,H⟩:= grammar A hp h
    let B:partX G r n d:=⟨honeyX p hp hx d, rollX _ _ hs H hx⟩
    have hh:B=A:=part_unique B A fun i g x=>by change honeyX _ _ _ _ _=_; rw [solid_mono _ hp hx,if_pos g,h]; exact grade_equal _ _ _ g
    exact congr_arg Subtype.val hh
end Script
end YM.OPE.Flume
