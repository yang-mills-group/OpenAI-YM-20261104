import YM.FormalBulk08.City.Palace

/-! All legs rotated. Quad Divergence. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.City
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries
open Lotus Shore Mesa Gorge
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} (s : Signed) {X : Type} {m r : ℕ} {n : Side}

def banner (k:Axis):ℝ:=if s.flip k then -1 else 1
def posStat {X : Type*}[AddCommGroup X][One X] (k : Axis) : Four X := if s.flip k then -step (s.perm k) else 0
def dart {X : Type} [AddCommGroup X][One X] (x:Pane G (Four X)):Pane G (Four X):=
   let k:=axisEquiv.symm x.2.1;(s.act x.1 + posStat s k,coord (s.perm k),x.2.2)
lemma dart_turn (v : Edge (Site n))(b:hue G) : dart s (v.1,coord v.2,b) = ((sendEdge s 0 v).1,coord (sendEdge s 0 v).2,b):= by
   have he : axisEquiv.symm (coord v.2)=v.2:=axisEquiv.symm_apply_apply _
   cases h : s.flip v.2 <;> simp [sendEdge,Step.used,Step.rotate,posDir,affine,h,dart,posStat,he,sub_eq_add_neg]
lemma darts : Injective (dart (G:=G) (X:=Per n) s) := by
   rintro ⟨x,i,b⟩ ⟨y,j,c⟩ h; obtain ⟨a,rfl⟩:=axisEquiv.surjective i; obtain ⟨k,rfl⟩:=axisEquiv.surjective j
   let u:Edge (Site n):=(x,a); let v:Edge (Site n):=(y,k)
   change dart s (u.1,coord u.2,b)=dart s (v.1,coord v.2,c) at h; rw [dart_turn,dart_turn] at h
   have he:u=v:=sendEdge_injective s 0 (Prod.ext (congr_arg (fun a:Pane G (Site n)=>a.1) h) (axisEquiv.injective (congr_arg (fun a:Pane G (Site n)=>a.2.1) h)))
   have hx: x=y:=congr_arg (fun a: Edge (Site n)=>a.1) he
   have hz: b=c:=congr_arg (fun a:Pane G (Site n)=>a.2.2) h
   have ht: a=k:=congr_arg (fun a:Edge (Site n)=>a.2) he
   rw [hx,hz,ht]
def displayed (G : Gauge) (s : Signed) (n : Side) : Matrix (wire G n) (wire G n) ℝ:= fun i=> Pi.single (dart s i) (banner s (axisEquiv.symm i.2.1))
def arc (G : Gauge)(s : Signed)(n : Side):Rays (wire G n)→L[ℝ]Rays (wire G n):=LinearMap.toContinuousLinearMap (displayed G s n).mulVecLin
lemma arc_read (j:wire G n)(z) : arc G s n z j=banner s (axisEquiv.symm j.2.1)*z (dart s j):= by
    change ∑ i, displayed G s n j i*z i=_; rw [Finset.sum_eq_single (dart s j)]; simp [displayed];intro b _ h; simp [displayed,h];simp
lemma arc_pull (U): Stationary.input G n (arc G s n U) = pull s 0 (Stationary.input G n U) := by
   funext j; have ht (b:G.ColorIndex) : arc G s n U (j.1,coord j.2,b)= banner s j.2 * U ((sendEdge s 0 j).1,coord (sendEdge s 0 j).2,b) := by rw [arc_read,dart_turn, show axisEquiv.symm (coord j.2)=j.2 from axisEquiv.symm_apply_apply _]
   have hh:(Stationary.arm G n 1 (arc G s n U)) (j.1,coord j.2)= banner s j.2 • (Stationary.arm G n 1 U) ((sendEdge s 0 j).1,coord (sendEdge s 0 j).2):= by ext b; exact ht b
   rw [Stationary.input,represent_link,hh]; unfold pull Step.read;split;next h=> rw [Stationary.input,represent_link,banner, if_pos (by simpa [Step.rotate,posDir] using h), neg_one_smul, exp_neg_color]; rfl
   next h=> rw [Stationary.input,represent_link,banner,if_neg (by simpa [Step.rotate,posDir] using h),one_smul]; rfl
lemma ringed (p : Pap (wire G n)) (h:Rite p p s 0)(e r):
   rancho p e r=pearl (displayed G s n) (rancho p e r) := by
   let R:=arc G s n; have ht:=h (wire G n) (fun z:Rays (wire G n)=>z ∘ id) R (fun _ _=>1) rfl (map_zero R) (show ContDiffAt ℝ ω (fun z:Rays (wire G n)=> z) 0 from contDiffAt_id) R.contDiff.contDiffAt (fun _=>contDiffAt_const) ⟨1,rfl⟩ (.of_forall fun z=>by unfold R;rw [arc_pull]; ext1 b;simp [Lattice.gauge])
   rw [Bank.pane_letter (displayed G s n) R R.contDiff.contDiffAt rfl] at ht
   have he := congr_arg (coeff e) ht; rw [fit_translate] at he; simp only [coeff_map] at he; change MvPolynomial.rename id _ = mixRows _ _ at he; rw [MvPolynomial.rename_id_apply] at he
   unfold rancho; rw [← target]; exact congr_arg (marble r) he
lemma compass (p:Pap (wire G n)) (h:Rite p p s 0) (e r) (w : chain (wire G n) r):
    rancho p e r (dart s ∘ w)=rancho p e r w * ∏ i,banner s (axisEquiv.symm (w i).2.1) := by
   nth_rw 1 [ringed s p h]; rw [pearl,tsum_fintype,Finset.sum_eq_single w]
   · simp [displayed]
   · intro b _ hb; have he : ∃ i,b i≠w i:=Function.ne_iff.mp hb; obtain ⟨i,hi⟩:=he;rw [Finset.prod_eq_zero (Finset.mem_univ i) (show displayed _ s n (b i) ((dart s ∘ w) i)=0 from by unfold displayed; rw [comp_apply,Pi.single_eq_of_ne ((darts s).ne (Ne.symm hi))]),mul_zero]
   simp
lemma arc_wrap (n : Side) (w : edgeL G): Lotus.drip n (dart s w)=dart s (Lotus.drip n w):= by
   cases h:s.flip (axisEquiv.symm w.2.1) <;> simp [dart, Lotus.drip,posStat,h]
lemma coastline (V: Tile (edgeL G) r)(P:(n:Side)→Pap (wire G n))(j : ℕ)(hp : Light V (fun n=>rancho (P n) j r)) (h : ∀ᶠ n in atTop,Rite (P n) (P n) s 0) (w : chain (edgeL G) r): V (dart s ∘ w)=V w*∏ i,banner s (axisEquiv.symm (w i).2.1) := by
   refine tendsto_nhds_unique (hp (dart s ∘ w)) (((hp w).mul_const _).congr' ?_); filter_upwards [h] with n hn; exact ((congr_arg (rancho (P n) j r) (funext fun k=>arc_wrap s n (w k))).trans (compass s (P n) hn j r (Lotus.drip n ∘ w))).symm

def Sworn (V : Tile (edgeL G) r) := ∀ (s : Signed)(w : chain (edgeL G) r),V (dart s ∘ w)=V w*∏ i,banner s (axisEquiv.symm (w i).2.1)
lemma named {T : Pot G} {M : Row (TypeFace 2) (TypeFace 2)}(h:Story T M) (j r : ℕ)(he:0<r) : Sworn (T j r) := by
   intro s w; obtain ⟨u,C,hu,hC⟩:=h.fare j r; apply coastline s _ (stone T) j _ (.of_forall fun n=> h.civic n s 0)
   simp_rw [h.flower _ r (⟨0,he⟩ : Fin r)]; exact (Bank.stable hu.le (h.civil j r) hC _).1
lemma lost_one {T : Tile (edgeL G) 1} (hv : Up T) (h : Sworn T) : T=0:= by
   funext v; let s:Signed:=⟨1,fun _=>true⟩; have he : dart s ∘ v= Lotus.tint ((dart s (v 0)).1-(v 0).1) ∘ v:= by
      ext1 j; rw [Subsingleton.elim j 0]; apply Prod.ext; exact (by simp); exact Prod.ext (axisEquiv.apply_symm_apply _) rfl
   have hx:=h s v; rw [he,hv] at hx; simp [s,banner] at hx;change T v=0; linarith only [hx]
lemma pillar {T : Pot G} {M : Row (TypeFace 2) (TypeFace 2)}(h:Story T M) (j : ℕ): T j 1=0:= lost_one (h.civil j 1) (named h j 1 Nat.one_pos)
lemma justice (T : Pot G)(a:hue G)(k: ℕ × ℕ)(hx : 0< k.2)(x: Cover) (h:T k.1 1=0): cruisesD a x k 1 T=0 := by
   have he (v:edgeL G)(l:Bool): shapeD a v l k 1 T=0 := by
       unfold shapeD; apply Finset.sum_eq_zero;intro j _; rw [plaster]; have hv:= Finset.mem_antidiagonal.mp j.property
       by_cases hp:j.val.2=k.2
       · rw [show shed (T k.1 (j.val.1+1)) v=0 from ?_, show clutch (_:Tile _ j.val.1) (hill a v l k.2 j.val.2)=0 from (by funext; simp [clutch]),sand_nil,length_void,smul_zero]
         rw [show j.val.1=0 by omega]; exact h ▸ rfl -- dependent cast issues
       rw [hill_empty a v l _ _ hp, show clutch (shed _ v) (0:Tile (edgeL G) j.val.2)=_ from ?_,sand_nil,length_void,smul_zero]
       funext;simp [clutch]
   simp [cruisesD,he]
lemma directP {T : Pot G} {M : Row (TypeFace 2) (TypeFace 2)}(h:Story T M) (j : ℕ) (a:hue G)(x:Cover): riverP a x (T j 2)=0:= by
   have ht := storied a h x j 1; rw [Finset.sum_eq_single (j,0),cruise_head _ _ _ (h.agate _ _)] at ht
   · exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
   · rintro ⟨p,q⟩ hp hv;rw [Finset.mem_antidiagonal] at hp; apply justice _ _ _ _ _ (pillar h _);change 0<q; simp only at hp; by_contra hb; subst_vars; exact hv (Prod.ext (by dsimp;omega) (by dsimp;omega))
   simp
end YM.FormalBulk08.City
