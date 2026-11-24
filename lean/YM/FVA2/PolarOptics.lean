import YM.FVA2.TurningPole
/-!
# Choose high-dimensional covariantization equivariant, including real and signed-axis action
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.FVA2.ArchTurn
open Filter Topology Set Function MeasureTheory MS MS.Logarithm MS.Land
open MS.Plane MS.Lifting MS.Landau MS.Landau.Detect MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program MS.Dock
open MS.Pearl MS.Train MS.Outlook MS.Mach MS.Arts MS.Arts.Spin MS.Halo MS.Arc MS.Garment MS.Hem MS.Rock MS.Rock.Path MS.Alps
open MS.Plane.Wire MS.Arts.Pilot MS.Rock.Oceans MS.Color MS.Shine MS.Hem.Mell ColorCode
open MS.Motif MS.Motif.Literal
open scoped Topology Classical ContDiff
variable {G:Gauge} (s: Signed) {m n h:ℕ} (F:Mob G) {u: ℤ} {z:ℂ} {k:Axis}
local notation "B"=> ColorCode.wings G
local notation "ℰ"=> ( Surf.orbit ( arcS n s ) G)
def flight (s:Signed)(i:Plaq): Plaq:= ⟨s.perm.symm i.i,s.perm.symm i.j,List.map s.perm.symm i.jets⟩
def catar (s:Signed)(i:Axis):ℝ:= cross (s.flip (s.perm.symm i)) true
private lemma sky_one {E:Type*}[AddCommMonoid E][Module ℂ E] (i:Axis)(U:L n→E) : ∑ j:L n, (ℰ).profile j (chair n i) • U j=(↑(catar s i):ℂ) • U (chair n (s.perm.symm i)):= by
   obtain he:= congr_arg (fun k:Axis=> chair n k ) (s.perm.apply_symm_apply i); rw [Finset.sum_eq_single_of_mem (chair n (s.perm.symm i)) (Finset.mem_univ _)]; · unfold Surf.orbit; dsimp only; rw [frames,pref,if_pos he,tape_i ]; rfl
   intro j _ hj; unfold Surf.orbit; dsimp only; rw [frames,if_neg (mt (fun h:(sky s n j)=chair n i => (sky s n).injective (h.trans ( ( (pref (n:=n) s (s.perm.symm i)).trans he ).symm))) hj),Complex.ofReal_zero,zero_smul]
private def tax (s:Signed)(i:Plaq):ℝ:= (i.jets.map (catar s)).prod*(catar s i.i*catar s i.j)
private lemma vault (f:Plaq): Surf.air ℰ (Pole_leaf (G:=G) (n:=n) z f)= (tax s f:ℂ) • Pole_leaf z (flight s f):= by
   obtain ⟨i,j,l⟩:= f; induction l with
   | nil=> unfold Pole_leaf tax flight; simp only [Pole,List.map_nil,List.prod_nil,one_mul,Surf.earth,sky_one]; push_cast; rw [mul_smul]
   | cons k l ih=> unfold tax flight Pole_leaf at *; simp only [ Pole, Surf.grip, sky_one,ih,map_smul, List.map_cons,List.prod_cons]; push_cast; simp only [mul_smul] -- maybe exact
private def taxes (m:ℕ)(s:Signed)(f:Fin m→Plaq): ℝ:= ∏ i:Fin m, tax s (f i)
private lemma train_c (m:ℕ)(f: Fin m→ Plaq)(j:Lifting.Grid G m) : canto s ( Pole.wing m f j z )= (↑(taxes m s f):ℂ) • Pole.wing m (flight s ∘ f) j z:= by
   induction m with
   | zero=>
       have he: taxes 0 s f=1:= Fin.prod_univ_zero _; rw [he,Complex.ofReal_one,one_smul]; exact funext fun n=> ( Surf.orbit ( arcS n s ) G).fixC 1
   | succ m ih=>
       let p:= arcS; let V:= Pole.wing m (f ∘ Fin.succ) (j ∘ Fin.succ) z;
       have he :taxes (m+1) s f= tax s (f 0)*taxes m s (f ∘ Fin.succ):= Fin.prod_univ_succ (tax s ∘ f); rw [he,Complex.ofReal_mul]; ext1 n; let N:= Surf.orbit (p n s) G; change N.run (bite n G (Pole_leaf z (f 0) (j 0)) (V n))= _; rw [ N.prod, show N.run _= _ from congr_fun (vault (n:=n) (G:=G) s (z:=z) (f 0)) (j 0), show N.run (V n) = _ from congr_fun (ih ( f ∘ Fin.succ ) ( j ∘ Fin.succ )) n, Pi.smul_apply,Pi.smul_apply, map_smul,map_smul,LinearMap.smul_apply, smul_comm (↑(taxes m s (f ∘ Fin.succ)):ℂ), mul_smul ]; rfl
private lemma saint_c (m:ℕ)(f: Fin m→ Plaq) (j:Lifting.Grid G m)(z:ℂ) : canto s ( Pole.saint m f j z)= (↑(taxes m s f):ℂ) • Pole.saint m (flight s ∘ f) j z:= by unfold Pole.saint; rw [map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,train_c,smul_comm]
lemma expands_s (W: Coat G)(he:W∈ Gallery G m h): tickW s W∈Gallery G m h:= by
   let V:= tickW s (G:=G); refine Submodule.span_induction (p:=fun W _=> V W∈ Gallery ..) ?_ ?_ ?_ ?_ he
   · rintro _ ⟨f,j,h,rfl⟩; rw [← h]; have hh: Pole.wage m (flight s ∘ f)=Pole.wage m f := (by simp [Pole.wage, Pole.Grit,flight]); rw [show V (Pole.saint _ _ _) =( taxes m s f:ℝ ) • Pole.saint m ( flight s ∘ f ) j from funext fun z=> saint_c s m f j z]; apply (Gallery G m (Pole.wage m f)).smul_mem; exact Submodule.subset_span (R:=ℝ) (s:=Sentence G m (Pole.wage m f)) (show ( Pole.saint m ( flight s ∘ f ) j )∈ Sentence G m (Pole.wage m f) from ⟨_,_,hh,rfl⟩)
   · rw [map_zero ]; exact (Gallery G m h).zero_mem
   · intro i j _ _ he hv; rw [map_add ]; exact Submodule.add_mem _ he hv
   intro c F _ he; rw [show V (c • F)=c • V F from map_smul (V.restrictScalars ℝ) c F]; exact (Gallery G m h).smul_mem _ he
abbrev polar := Literal.Boom 0 (canto (G:=G) s)
lemma raises {V:Box (Mob G)}{H: Law G} (he: Ele h n H V): Ele h n (SpinCode.backlit s H) (polar s V):= by
   refine ⟨ ?_, ?_⟩; · unfold polar; simp_rw [ linear_v ]; exact expands_s s _ he.1
   rw [show polar s V 0= canto s ( V 0 ) from whole ..]; change whorl 0 s (V 0 0)= _; rw [ he.2,ceiling0 ]
lemma polar_c (r:Signed)(V: Box (Mob G)) : polar r (polar s V)= polar (s*r) V:= by
   have he (V:Box (Mob G))(s:Signed)(n:ℕ): polar s V n=canto s (V n):= whole ..; ext1 i; rw [he,he,he]; ext n l; change (leggo _ (arcS n r)).beam ((leggo _ (arcS n s)).beam (V i n)) l=(leggo _ (arcS n (s*r))).beam (V i n) l; rw [ fuses,forever ]
-- relation to cost V.Book Lam Must fit raw.
open MS.Native MS.Native.Paint Lattice MS.Tone MS.Tone.Frame MS.Native.Wilsonian MS.Native.Orient MS.Menus MS.SpinCode
private lemma face_t {f H: Law G}(he: Face wfield f H u false): Face wfield (whorl 0 s f) (whorl 0 s H) u false:= by
   intro l ht; let f' := l.map ( remode s ); have hv(t:ℝ): sail (ray f') t=(sail (ray l) t).map (remode s):= by unfold f' sail ray; simp only [List.map_map]; congr! 1; funext i; exact Prod.ext rfl ( (map_smul (arcS 0 s).turn t i.2).symm );
   have hb (t:ℝ): stem s (sail (ray l) t)= stem s l:= by unfold stem sail ray; rw [List.map_map,List.map_map ]; rfl
   obtain he:= he f' (fun v=> Bool.noConfusion v); have hu: fieldDim wfield f'=fieldDim wfield l:= by
      unfold fieldDim f'; simp only [List.map_map,comp_def]; apply congr_arg List.sum; congr! 1
   rw [hu] at he; unfold fieldVal; simp_rw [ sprint s, hb, ← hv ]; exact he.smul _
lemma fitsWh {F: Native.Dot G Cover}{H: Law G}(hf:Lifting.Fits F H m u false): Fits ( Native.Orient.pose s F ) (whorl 0 s⁻¹ H) m u false:= by
   unfold Fits; rw [SpinCode.startL,rotD, ← ceiling0, whorl,show mask (m:ℤ) ((flagS _ G).beam ( Tone.run F ))=_ from (beam_mask (flagS (arcS 0 s⁻¹) G) _ _).symm ]; exact face_t s⁻¹ hf
lemma Fits_only {H L: Law G}{M: Native.Dot G Cover} (hf:Lifting.Fits M H m u false)(ht:Lifting.Fits M L m u false): H=L:= by
   ext l; let p:=u - fieldDim wfield l; by_cases hx:p<0; · rw [(hf l (fun u=> Bool.noConfusion u)).bottom hx, (ht l (fun u=> Bool.noConfusion u)).bottom hx ]
   have hv: u-fieldDim wfield l=(p.toNat:ℤ):= (by omega); rw [← if_pos hv.symm (t:= H l) (e:=0), ← if_pos hv.symm (t:=L l) (e:=0), ← (hf l (fun u=> Bool.noConfusion u)).home _ hv.symm.le,← (ht l (fun u=>Bool.noConfusion u)).home _ hv.symm.le]
variable (V: Warehouse G)
local notation "vID"=> Plaid (wings G) h
lemma height_c (i: Plaid (wings G) h) : SpinCode.backlit s⁻¹ ( Land.read i ).read= ∑ j:Plaid (wings G) h,(ColorCode.fee V.F s.ortho h i j:ℂ) • ( Land.read j ).read := by
   let p:Team:= fun _=> ⟨0,0,0⟩; let J (i: Plaid B h):= Land.read i; let K (i:BasisIx G h):= Glyph.preambleM (V.native (wings G)) p i 0; rw [ ← ceiling0 ]; obtain hf:= fitsWh s ( Glyph.pre_floorM (V.native (wings G)) p (J i) 0 ); refine Fits_only hf ?_;
   change Fits (Native.Orient.pose s (K (J i) 0) ) _ _ _ _; obtain hh: Native.Orient.pose s (K (J i) 0)= ∑ j:vID,(ColorCode.fee V.F s.ortho h i j:ℂ) • K (J j) 0 := by
       have hh := congr_fun ( purpose h V p s 0 (J i) ) 0; change pose s (K _ _)=_ at hh; rw [ hh, Finset.sum_apply ]; simp_rw [Pi.smul_apply, held_real ]; refine Eq.trans ( tag_survives h _ ?_ ) ?_; swap; · rfl
       intro u H; rw [ shown_off V.F s.ortho h (J i) u (fun h=> H ( Eq.symm (congr_arg Prod.fst h) )), zero_smul ]
   rw [hh]; refine Fits.sum _ (fun j _=>?_ ); by_cases hj:( J i ).grade=(J j).grade; · rw [hj]; exact ( Glyph.pre_floorM (V.native _) p ( Land.read j ) 0).smul _;
   rw [ColorCode.fee,held_real, shown_off _ _ _ _ _ (fun h=>hj (congr_arg Prod.snd h)),zero_smul,zero_smul ]; -- both rw zero
   exact Fits.zero _
-- reuse ArchTurn polarity for precise chosen Gallery
def Spun (s: Signed)(i:Plaq):ℝ:= (i.jets.map (catar s)).prod*(catar s i.i*catar s i.j)
lemma rotation (m:ℕ)(f: Fin m→ Plaq) (j:Lifting.Grid G m)(z:ℂ) : canto s ( Pole.saint m f j z)= ( Complex.ofReal (∏ i:Fin m,Spun s ( f i )) ) • Pole.saint m (flight s ∘ f) j z:= saint_c s m f j z
end YM.FVA2.ArchTurn
