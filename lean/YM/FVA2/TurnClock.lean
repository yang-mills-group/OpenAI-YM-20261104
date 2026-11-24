import YM.FVA2.TurnAct
/-!
# Transport the `scoreM` high mode evolution in the angular conventions

Use only **net=0** in the unmarked arguments and no such qualification in the
marked procedure. Rotate an arbitrary *picked solution*, not the internals
of the step selection functions; this lets one average later.
-/
set_option autoImplicit false
set_option maxHeartbeats 830000
noncomputable section
namespace YM.MS.SpinCode
open Function Filter Set Finset Plane Koszul Flux MeasureTheory City High
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect
open Complex (I)
open Book Convolve Program Native.Wilsonian Native.Paint Native.Orient
open Wind High.Knobs
open scoped Topology ContDiff
variable {G:Gauge} (s:Signed) {b:Bool} {F H: Law G} {v z:ℤ} {t:Team}
variable {K X:Wind.Dec G}{Y W:ℂ} {n h r:ℕ}

-- linear operator throughout scales
abbrev rotD (s:Signed)(F:Law G): Law G := backlit s⁻¹ F
abbrev turnF (f:Wind.Flow G): Wind.Flow G:= fun x=> rotD s (f x)
def αV (s:Signed) : QP→L[ℝ]QP:= (Outlook.hand s ).turn.toContinuousLinearMap
lemma αhere (p:QP): αV s p=s.act p:=rfl
lemma reprice_inv (M:Lane4 G) : permute s (permute s⁻¹ M)= M:= by rcases M with ⟨⟨⟨_|a,_|_⟩,i⟩,k⟩ <;> simp [permute]
lemma signage_inv (M:Lane4 G): negateField s (permute s⁻¹ M)= negateField s⁻¹ M:= by rcases M with ⟨⟨⟨_|a,_|_⟩,i⟩,k⟩ <;> simp [negateField,permute]
lemma shift_back (F:Law G) : backlit s⁻¹ (backlit s F)= F:= by
   funext l; rw [awarded,awarded,← mul_assoc, show SideS s (l.map ( permute s⁻¹ ))= SideS s⁻¹ l from ?_, twice_S,one_mul, show (l.map (permute s⁻¹)).map (permute s)=l from ?_ ]; · simp [Function.comp_def,reprice_inv]
   simp [SideS,Function.comp_def,signage_inv]
lemma startL (x:Dot G Lattice.Cover): run (pose s x)=rotD s (run x):= by unfold rotD; rw [← pinΓ (G:=G) s x, shift_back ]
private lemma turn_tag (T:Wind.Flow G)(h:TouchF T): TouchF (turnF s T):= by
   intro E _ _ f w hw ht; let R := s⁻¹; let l:= w.map fun i=>(passN R i.1,αV R ∘ i.2); have he (x:E): turnF s T (f x) (walk0 w x)= (w.map fun i=> tick R i.1).prod*T (f x) (walk0 l x):= by
       unfold turnF rotD l; rw [ awarded ]; congr 1; unfold SideS walk0; simp only [List.map_map]; rfl; simp [walk0, Function.comp_def, passenger,αhere,R]
   simp_rw [he]; apply ContDiff.mul contDiff_const; refine h E f _ ?_ ht; intro i hi; obtain ⟨a,ha,rfl⟩:= List.mem_map.mp hi; exact (αV _).contDiff.comp (hw a ha)
private lemma circle_turn (f:Wind.Flow G)(hf:TouchF f)(x:ℝ): Wiref G (turnF s f) x=rotD s (Wiref G f x):= by
   change Heat.orbit _ _ (turnF s f x)= rotD s (Heat.orbit (Cpu G x) _ (f x)); rw [ finite_cc μzone (period0 μzone cour0 (main_f _) (turn_tag s f hf)), finite_cc μzone (period0 μzone cour0 (main_f _) hf) ]; exact (mist_cc s⁻¹ (K_cpu ..) _).symm
private lemma shiftSat (f P:Wind.Flow G)(u:Law G)(hh:TouchF f)(hp:Wind.Sat u f P): Wind.Sat (rotD s u) (turnF s f) ( turnF s P ):= by
    refine ⟨congr_arg _ hp.1, fun t w=>?_⟩; rw [ circle_turn s f hh t]; change HasDerivAt (fun t=>(turnF s f) t w) (_+_) t; simp_rw [turnF,rotD,awarded]; exact (HasDerivAt.congr_deriv ((hp.2 t (w.map (permute s⁻¹))).const_mul (SideS s⁻¹ w)) (mul_add ..))
lemma force_turn (K X Y:Wind.Dec G)(x:ℝ)(hq:∀ i∈Domain.paths n r,Y i x=turnF s ( X i x ))(he:∀ i, Fees true v (K i)): path 1 n r K Y x = turnF s (path 1 n r K X x):= by
   funext t; unfold turnF rotD path; simp only [one_smul,Finset.sum_apply,map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [hq i hi]; exact shadow_tree s⁻¹ (K_cpu ..) ((he (n-i)).stay x|>.stand t rfl)

section binds
variable (A:Team) (U:Wind.Dec G) (V:T (ℝ→Law G))
-- We only need the *linear* comparison mode of PM. No estimate except for testing
-- uniqueness of V columns at fixed power (Fees & Moment bound in Main theorem).
structure Tick (A:Team) (U:Wind.Dec G) (V:T (ℝ→Law G)) : Prop where
    solves n (x:ℝ) : Sat (V n x) (U n x) (path 1 n 0 (Wind.skyline G A) U x)
    orient n (x:ℝ): TouchF (U n x)
    tally n (x:ℝ) : ∃ a:ℤ, Rank (U n x) a
lemma ticksM (u:Actor G)(q:ℤ)(h:PM u (skyline G A) U q): Tick A U (fun n x=> run (u x n)) where
    solves n x := h.recu n x
    orient n x:= ( h.owes n |>.stay x ).joint
    tally n x:=by obtain ⟨i,v⟩:= ( h.owes n ).pay; exact ⟨ i,v x ⟩
namespace Tick
variable {U V A}
def shiftS (s:Signed)(Q:Wind.Dec G): Wind.Dec G:= fun n x=> turnF s (Q n x)
lemma shifted (h:Tick A U V): Tick A (shiftS s U) (fun i x=> rotD s (V i x)) where
    solves n x:= by rw [force_turn s (v:=0) (skyline G A) U _ x (fun i _=>rfl) (skyPC G A|>.owes)]; exact shiftSat s _ _ _ (h.orient n x) (h.solves n x)
    orient n x:= turn_tag s _ (h.orient n x)
    tally n x:= by obtain ⟨i,v⟩:= h.tally n x; exact ⟨i,fun t w hw=> by unfold shiftS turnF rotD; rw [awarded,v t _ (by simpa using hw),mul_zero]⟩
lemma plus {M Z}(h:Tick A U V)(he:Tick A M Z) : Tick A (U+M) (V+Z) := by
    have hQ(i:ℕ)(x:ℝ): path 1 i 0 (skyline G A) (U+M) x= path 1 i 0 (skyline G A) U x+path 1 i 0 (skyline G A) M x:= by unfold path; simp only [one_smul,Finset.sum_apply,Pi.add_apply,map_add,Finset.sum_add_distrib]
    refine ⟨fun n x=> ?_, fun n x=> (h.orient n x).add (he.orient n x), fun n x=> ?_⟩
    · rw [hQ]; obtain ⟨h1,hH⟩:= h.solves n x; obtain ⟨h2,hT⟩:= he.solves n x; refine ⟨congr_arg₂ (·+·) h1 h2,fun t=>?_⟩; change Zip (_ + _) _ t; convert! Zip.add (hH t) (hT t) using 1; simp only [Pi.add_apply,map_add]; abel
    obtain ⟨a,ha⟩:= h.tally n x; obtain ⟨c,hc⟩:= he.tally n x; exact ⟨ max a c, Rank.add (ha.pay (le_max_left ..)) (hc.pay (le_max_right ..)) ⟩
lemma weight (h:Tick A U V)(x:ℂ): Tick A (x • U) (x • V) := by
    refine ⟨fun n y=> ?_,fun n y=> (h.orient n y).scale x,fun n y=> by obtain ⟨i,hi⟩:=h.tally n y; exact ⟨i,(hi.smul x)⟩⟩
    have he:path 1 n 0 (skyline G A) (x • U) y=x • path 1 n 0 (skyline G A) U y:= by unfold path; simp only [one_smul,Finset.sum_apply,Pi.smul_apply,map_smul, Finset.smul_sum]
    obtain ⟨hV,hF⟩:= h.solves n y;
    rw [ he]; refine ⟨congr_arg (x • ·) hV,fun t=>?_⟩; convert! Zip.scalar (hF t) x using 1; simp only [Pi.smul_apply,map_smul,smul_add]
lemma zero : Tick A 0 (G:=G) 0:=by refine ⟨fun n x=> ⟨ rfl,fun t w=>?_⟩,fun _ _=>TouchF.zeros,fun _ _=>⟨_,Rank.zero G 0⟩⟩; simp only [Pi.zero_apply,map_zero,path,Finset.sum_apply,Finset.sum_const_zero,one_smul,add_zero]; exact hasDerivAt_const ..
lemma total {A':Type}{U:A'→ Wind.Dec G}{f:A'→ T (ℝ→Law G)}(S: Finset A')(h:∀ i∈S, Tick A ( U i ) ( f i )): Tick A (∑ i∈S,U i) (∑ i∈S,f i):= by classical induction S using Finset.induction_on with| empty=> rw [ Finset.sum_empty,Finset.sum_empty ]; exact Tick.zero| insert i S hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h i (by simp)).plus ( ih (fun i h'=> h i ( mem_insert_of_mem h' )) )
lemma unique {X:Wind.Dec G}(he:Tick A X V)(hv: Tick A U V): X=U:= by
   funext n; induction n using Nat.strongRecOn with | ind n ih=>
    funext x; apply sub_eq_zero.mp; obtain hP:=he.solves n x; obtain hF:=hv.solves n x; rw [path_eq 1 _ _ (fun _ _=>rfl) (F:=skyline G A) (Q:=X) (W:=U) (fun i hi=>ih i (Wind.path_in hi).2)] at hP
    refine Dtotal ⟨?_ ,?_, fun t w _=>?_⟩ ?_
    · have ht: TouchF (- (U n x)):= by simpa only [neg_one_smul, Pi.neg_def] using (hv.orient n x).scale (-1:ℂ); -- name
      rw [sub_eq_add_neg]; exact (he.orient n x).add ht
    · obtain ⟨a,ha⟩:= he.tally n x; obtain ⟨c,hc⟩:= hv.tally n x; exact ⟨ max a c, Rank.sub (ha.pay (le_max_left ..)) (hc.pay (le_max_right ..)) ⟩
    · convert! (hP.2 t w).sub (hF.2 t w) using 1; rw [map_sub]; simp only [Pi.sub_apply,Pi.add_apply]; abel
    rw [Pi.sub_apply,hP.1,hF.1,sub_self]
end Tick
end binds
section trust
variable {F M R W:Recount G}
private lemma actionLike {Z V:Reading G} (h:Trust false v Z V r): Trust false v (rotD s ∘ Z) (rotD s ∘ V) r:= by
    intro E _ _ w _ hr; let T:=αV s⁻¹; let U : Wire (Branch G Axis) E FourP:= w.map fun i=> (passN s⁻¹ i.1, T.comp i.2); obtain he:= h E U (fun v=>Bool.noConfusion v) (by simp [U,hr]); let p:ℂ:=(w.map fun i=> tick s⁻¹ i.1).prod; let C:= ContinuousLinearMap.mul ℝ ℂ p;
    have ht (q:Reading G): Chart (lane meet (rotD s ∘ q)) w = fun i x=> C (Chart (lane meet q) U i x):= by
       funext i y; unfold Chart lane rotD; dsimp only [Function.comp_apply]; rw [awarded];
       change SideS _ _*q _ _= p* q _ _; congr 1; unfold SideS sail p; simp only [List.map_map]; rfl
       simp [sail,U,Function.comp_def, City.passenger, T,αhere]
    have hi: fieldDim wfield w=fieldDim wfield U:= by simp only [fieldDim,U,List.map_map]; rfl
    unfold Light at *; rw [ht,ht,hi]; exact he.L _
def flipScore (s:Signed)(F:Recount G): Recount G:= fun i=> rotD s ∘ F i
lemma winds {n:ℕ}(h: Fixed F W false v n): Fixed (flipScore s F) (flipScore s W) false v n:= fun i hv r hr=> actionLike s (h i hv r hr)
lemma records {n:ℕ}(h:Fixed F W false v n)(hp: Fixed M R false v n): Fixed (F+M) (W+R) false v n:=fun i hi r hr E _ _ w hw hx=> Like.add (h i hi r hr E w hw hx) (hp i hi r hr E w hw hx)
lemma presses {n:ℕ}(h:Fixed F W false v n)(p:ℂ): Fixed (p • F) (p • W) false v n := fun i hi r hr E _ _ w hw hx=> Like.L (h i hi r hr E w hw hx) (ContinuousLinearMap.mul ℝ ℂ p)
lemma narration {n:ℕ}{V:Type*}{A B:V→Recount G}(x:Finset V)(hp:∀ i∈x,Fixed (A i) ( B i ) false v n): Fixed (∑ i∈x,A i) (∑ i∈x,B i) false v n:= by
    classical
    induction x using Finset.induction_on with| empty=> simp only [Finset.sum_empty]; exact fun n _ _ _=> zero_ext (fun _ _ _ _=>rfl) (fun _ _ _ _=>rfl)| insert i x h ih=> rw [Finset.sum_insert h,Finset.sum_insert h]; exact records (hp _ (by simp)) (ih (fun _ hv=>hp _ (Finset.mem_insert_of_mem hv)))
end trust
end YM.MS.SpinCode
