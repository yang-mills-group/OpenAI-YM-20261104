import YM.SchemeConversionRG11.FirstW.Hart.Plan
/-! Signed-chart transformations of highest cochain responses in native polynomial slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Set Lattice Pert Align Topology Maxwell Next.Rank.CellsInt
open scoped BigOperators Classical
open Push.FiniteDetection.Free.Hyper hiding flip pull
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Gauge} {j : ℕ}
abbrev violet := Push.FiniteDetection.Free.Hyper.flip
def bottomK (s : Signed) (b : Axis) : Cover := if s.flip b then -step (s.perm b) else 0
lemma strand (s : Signed) (i : Axis) (v : Cover) (A : Field4 G) : field4 i (Bare.wideLink G s A) v = violet s i • field4 (s.perm i) A (s.act v+bottomK s i) := by simp only [field4,Bare.wideLink_apply]; cases h:s.flip i <;> simp [violet,Push.FiniteDetection.Free.Hyper.flip,posDir,Step.rotate,Step.used,bottomK,h,sub_eq_add_neg]
lemma east_com (s : Signed) (i : Axis) (f : Cover→E) (u : Cover) : up i (fun v : Cover=> f (s.act v+u)) = fun v=> violet s i • up (s.perm i) f (s.act v+(bottomK s i+u)) := by
   funext v; simp only [up, s.act_add]
   have e := Step.vec_rotate (R:=ℤ) (posDir i) s; rw [Step.vec_pos] at e; rw [←e]
   cases h:s.flip i <;> simp [Step.vec,Step.rotate,violet,Push.FiniteDetection.Free.Hyper.flip,posDir,bottomK,h, add_left_comm,add_comm]
def slate (s : Signed) (D : List Axis) := (D.map (fun i=>violet s i)).prod
def breeze (s : Signed) (D : List Axis) := ((D.map (bottomK s)).sum)
lemma propel (s : Signed) (D : List Axis) (f : Cover→E) (u : Cover) : combine D (fun v : Cover=> f (s.act v+u)) = fun x=> slate s D • combine (D.map s.perm) f (s.act x+(breeze s D+u)) := by
  induction D generalizing f u with
  | nil=> simp [slate,breeze,combine]
  | cons a t ih=>
    rw [combine, ←combine_up, east_com]; rw [show (fun x=> (violet s a) • up _ f (s.act x+_))=(violet s a) • (fun x:Cover=> up (s.perm a) f (s.act x+(bottomK s a+u))) from rfl]; rw [combine_smul, ih, List.map_cons]; funext v
    simp only [Pi.smul_apply,slate,List.map_cons,List.prod_cons,breeze, List.sum_cons, smul_smul,combine_up,combine,add_assoc,add_left_comm (bottomK s a)] -- reorder
lemma track_stor (s : Signed) (A : Field4 G) (hA : A∈stor G j) : Bare.wideLink G s A∈stor G j := by
  refine stor_mem.mpr fun i D hD=> ?_
  rw [show field4 i (Bare.wideLink G s A)= violet s i • _ from funext (strand s i · A), combine_smul] -- infer ?
  rw [propel,stor_mem.mp hA (s.perm i) _ (by rw [List.length_map,hD])]; ext1; simp
lemma rotLap (s : Signed) (i : Axis) (x : Cover) (A : Field4 G) : atoneLap (field4 i (Bare.wideLink G s A)) x= violet s i • atoneLap (field4 (s.perm i) A) (s.act x+bottomK s i) := by
  unfold atoneLap; rw [Finset.smul_sum]; refine Fintype.sum_equiv s.perm _ _ ?_; intro k
  simp_rw [strand,Signed.act_add,Signed.act_sub]; have e := Step.vec_rotate (R:=ℤ) (posDir k) s; rw [Step.vec_pos] at e; rw [←e,smul_sub,smul_add,smul_comm _ (2:ℕ)];
  cases h : s.flip k <;> simp only [Step.vec,Step.rotate,posDir,h,Bool.false_xor,Bool.false_eq_true,↓reduceIte, ← sub_eq_add_neg]
  · congr 3 <;> abel
  · simp only [sub_neg_eq_add]; rw [add_comm (violet s i • _)] -- swaps smuls?
    congr 3 <;> abel
lemma rewind (s : Signed) (i : Axis) (x : Cover) (A : Field4 G) :
    field4 i (Bare.wideLink G s A) x- field4 i (Bare.wideLink G s A) (x-step i) = field4 (s.perm i) A (s.act x)-field4 (s.perm i) A (s.act x-step (s.perm i)) := by
  simp_rw [strand, Signed.act_sub]; have e:=Step.vec_rotate (R:=ℤ) (posDir i) s; rw [Step.vec_pos] at e; rw [← e]; cases h : s.flip i <;> simp [Step.vec,Step.rotate,posDir,h,violet,Push.FiniteDetection.Free.Hyper.flip,bottomK,sub_eq_add_neg,add_comm]
lemma track_cabin (s : Signed) (A : Field4 G) (hA : A∈cabin G j) : Bare.wideLink G s A∈cabin G j := by
  refine ⟨track_stor s _ (cabin_stor hA), fun i=>?_,?_⟩
  · funext x; rw [rotLap, cabin_lap hA]; exact smul_zero _
  funext x; exact (Fintype.sum_equiv s.perm _ _ fun i=> rewind s i x A).trans (congrFun (cabin_div hA) (s.act x)) -- Fintype
-- highest updates on already-curled rows
def curlK (A : Field4 G) (i j : Axis) := fun x:Cover => Bare.wideCurl A x i j
lemma curl_axis (A : Field4 G) (i j:Axis) (x:Cover) : curlK A i j x = up i (field4 j A) x -up j (field4 i A) x := by dsimp only [curlK,up,Bare.wideCurl,field4]; abel
lemma slide_curl (A : Field4 G) (s : Signed) (i j : Axis) : curlK (Bare.wideLink G s A) i j = (violet s i * violet s j) • (fun x:Cover=>curlK A (s.perm i) (s.perm j) (s.act x+(bottomK s i+bottomK s j))) := by
  funext x; rw [curl_axis]
  have he (i j:Axis) : up i (field4 j (Bare.wideLink G s A)) x= violet s j • (violet s i • up (s.perm i) (field4 (s.perm j) A) (s.act x+(bottomK s i+bottomK s j))) := by
      have H:=congrFun (east_com s i (field4 (s.perm j) A) (bottomK s j)) x
      rw [← H]; simp only [up,strand, smul_sub]
  simp only [he,Pi.smul_apply,curl_axis,smul_sub,smul_smul, add_comm (bottomK s j) (bottomK s i), mul_comm (violet s j) (violet s i)]
lemma jumped (s : Signed) (j : ℕ) (f : Cover→E) (H : f∈Loft E j) (a : Fin j→Axis) (x : Cover) : jumps j a (fun v=>f (s.act v+x)) 0 = (∏ i:Fin j,violet s (a i)) • jumps j (s.perm ∘ a) f 0 := by
  rw [jumps_eq,propel,jumps_eq]; unfold slate; simp only [Signed.act_zero,zero_add, List.map_ofFn, List.prod_ofFn]; exact congrArg (fun v=> (∏ i, violet s (a i)) • v) (loft_basis (loft_scoped j 0 _ (by simpa using H) _ List.length_ofFn) _)
end YM.RG11.FirstW
