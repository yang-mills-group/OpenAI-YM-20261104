import YM.SchemeConversionRG11.FirstW.Lien.Feather
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Lattice Pert Align Topology Deck Maxwell Extra.FD RawLabels Position SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical
variable {G:Gauge}{F : Labels.Frames G}{S:Itinerary}
variable {w:ℕ→Bond F} {i:ℕ}
lemma cup_level (h:fitsM S w) (H:Bond F→ₗ[ℝ] Pack F) (hp : ∀ v:Bond F,v∈ mask F (i+1) → H v=0) (he:i ≤ 4) : Level (fun j=> S.gap j • H (w j)):=by
 intro L
 let Z:=fun j=> S.gap j • w j
 let I:= {q:CheckQ F// q.i+q.j ≤ i} -- temp
 have hw : Tendsto (fun j=>(L.comp H) (Z j)) atTop (𝓝 0) := by
   refine @slicer _ _ _ _ I (fun s=>rate s.val) (L.comp H) ?_ Z ?_
   · intro v hv; rw [LinearMap.comp_apply,hp, map_zero]; exact fun s hs=>hv ⟨s,Nat.lt_succ_iff.mp hs⟩
   intro x
   have hh : (fun j=>rate x.val (Z j))=(fun j=> S.gap j • rate x.val (w j)):= funext fun j=> map_smul ..
   rw [hh]; exact h x.val (x.property.trans he)
 exact hw.congr (fun j=>by simp only [Z,LinearMap.comp_apply,map_smul])
lemma tollC (H:Bond F→ₗ[ℝ] Pack F) (hp:∀ v:Bond F,v∈mask F i⊓hum F (i+1) → v-glyph F (H v)∈mask F (i+1)) (h:paidC S i w) (ht:i ≤4) (hv:kissC S w) (s:CheckQ F) (hs:s.i+s.j=i) : Helen (fun j=> (S.gap j ^(4-i))⁻¹ • rate s (w j-glyph F (H (w j)))):=by
 let Z (j:ℕ):=(S.gap j ^ (4-i))⁻¹ • w j; let B:= rate s ∘ₗ (LinearMap.id- (glyph F).comp H)
 have hh(j:ℕ) : B (Z j)=(S.gap j ^(4-i))⁻¹ • rate s (w j-glyph F (H (w j))) := by rw [show B (Z j)=_ from B.map_smul ..];rfl
 simp_rw [← hh]
 let I := {x:CheckQ F//x.i+x.j < i ∨ x.i+x.j ≤ i ∧ quietly x.a.val}
 refine gathering (E:=Bond F) (I:=I) (fun s=>rate s.val) B ?_ Z ?_
 · intro v hw
   have L : v∈mask F i⊓hum F (i+1):= ⟨fun s hs=>hw ⟨s,Or.inl hs⟩,fun s hs ht=>hw ⟨s,Or.inr ⟨Nat.lt_succ_iff.mp hs,ht⟩⟩⟩
   exact hp v L s (hs.trans_lt (Nat.lt_succ_self _))
 rintro ⟨x,hx⟩
 change Helen (fun j=>rate x (Z j)); simp only [Z,map_smul]
 rcases hx with hx|hx
 · exact higherH (S:=S) (a:=4-i) (b:=4-(x.i+x.j)) (by omega) (h _ hx x rfl)
 exact higherH (S:=S) (a:=4-i) (b:=4-(x.i+x.j)) (Nat.sub_le_sub_left hx.1 _) (hv _ (hx.1.trans ht) x rfl hx.2)
lemma funds_bath (hp : paidC S i w) (ht:i≤4)(hr:fitsM S w)(he:kissC S w) : ∃ y:ℕ→ Pack F, Level (fun j=> S.gap j • y j) ∧ paidC S (i+1) (fun j=> w j-glyph F (y j)) := by
 obtain ⟨H,h,hA,hP⟩:=coverPk i ht F
 refine ⟨fun j=>H (w j),cup_level hr H h ht,?_⟩
 intro k hk q hq
 rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with ht'|ht'; swap; · rw [ht']; exact tollC H hA hp ht he q (by omega)
 have hh (j:ℕ) : rate q (glyph F (H (w j)))=0:= hP _ q (hq.trans_lt ht')
 simp only [map_sub,hh,sub_zero]; exact hp k ht' q hq
lemma lowCost {E:Type*}[AddCommGroup E][Module ℝ E][FiniteDimensional ℝ E] {z:ℕ→E} (f:E→ₗ[ℝ]ℂ) (h:Level z): Tendsto (fun j=> f (z j)) atTop (𝓝 0) := by
 let b:= Module.finBasis ℝ E; have ht (x:E): f x=∑ i,b.coord i x • f (b i) := by nth_rw 1 [←b.sum_repr x]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> f.map_smul ..
 have he := tendsto_finsetSum (s:=Finset.univ) (fun i _=>(h (b.coord i)).smul_const (f (b i)))
 simp only [zero_smul,Finset.sum_const_zero] at he; exact he.congr (fun j=>(ht _).symm)
lemma wPays (h:Level (fun j=> S.gap j • w j)) : fitsM S w := fun q _ => by simp only [← map_smul]; exact lowCost _ h -- U unused
lemma fits_current (p:ℕ→Pack F)(h:Level (fun j=>S.gap j • p j))(hp:fitsM S w): fitsM S (fun j=>w j-glyph F (p j)) := by
 have hh:= Level.map (V:=Bond F) (glyph F) h; simp only [map_smul] at hh
 intro x hx; simpa only [map_sub,smul_sub,sub_zero] using (hp _ hx).sub (wPays (S:=S) hh _ hx)
lemma kisses (hp:kissC S w)(p:ℕ→Pack F): kissC S (fun j=>w j-glyph F (p j)):=by
 intro i hi q hq hr
 simp only [map_sub,show ∀ j,rate q (glyph F (p j))=0 from fun _=> song_dead _ _ _ _ hr,sub_zero]; exact hp _ hi _ hq hr
theorem performs (W:ℕ→Bond F)(hf:fitsM S W)(hP:kissC S W): ∃ p:ℕ→Pack F, paidC S 5 (fun j=> W j-glyph F (p j)) ∧ Level (fun j=> S.gap j • p j) := by
 have he (i:ℕ)(hp:i≤5): ∃ p:ℕ→Pack F, paidC S i (fun j=> W j-glyph F (p j)) ∧ Level (fun j=> S.gap j • p j) := by
   induction i with
   | zero=> refine ⟨fun _=>0, fun j hj=>by omega, fun q=>?_⟩; simp
   | succ i ih=>
     obtain ⟨p,H,h⟩:= ih (by omega)
     obtain ⟨r,B,b⟩:= funds_bath H (by omega:i≤4) (fits_current p h hf) (kisses hP p)
     refine ⟨p+r, ?_,?_⟩
     · simpa only [Pi.add_apply,map_add,← sub_add_eq_sub_sub] using b -- maybe sub_add_eq?
     simp only [Pi.add_apply,smul_add]; exact Level.plus h B
 exact he 5 le_rfl
end YM.RG11.FirstW
