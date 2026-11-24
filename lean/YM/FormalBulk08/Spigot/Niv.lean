import YM.FormalBulk08.Spigot.Ebon
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius
variable {o:Loc G 1}{K:KernelChoices}{l d R:ℕ}{T:Anthem D G}
open Dove Dove.Lab North Drift Elm Aster Source Drops Labels
lemma sliced (hx:e≤E)(p:Studio D): Drift.sliceM T E p e=T p e:=if_pos hx
lemma testament {n:Side}(p:Studio D) (h:Sonority T T l 1 E): Glare (Kemp.banner l (sliceM T E p) n) E:= by
    have ht: Through E (Kemp.banner l (T p) n) (Kemp.banner l (sliceM T E p) n):=by intro j hj; simp_rw [Kemp.banner,coeff_mk,sliced hj p]
    intro I i a b k ha hb hA hB hK hp hx; refine (Through.change_congr (insertAt ℝ _) ht).symm.trans (Through.trans ?_ (Through.change_congr (insertAt ℝ _) ht)); change Through E (roam ℝ (motor a) _) (roam ℝ (motor b) _); simpa only [froth_self] using (h n p I a b k ha hb hA hB hK hp hx)
lemma glyph_limit {I:Type}{F:Lab G K I}{B:Frame G d}{H:Source.Hol G}{T: Source.SectionData B}{ρ:ChartRatio G}(q:Quota B H F o D E R)(u:Use F ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)(i:Letter B)(x:Leaf F.scrolls): Glyph o (sliceM (Drift.issue F ρ a B T q.horizon x.a x.b i) E) (Pose.slots B i) E:= by
   obtain ⟨he,hx⟩:=rations_limit q u h a hs ht hb hr i x; exact ⟨hx,he,fun _ p=> testament p (single_convention q u h a hs ht hb hr i x)⟩
lemma timber {I:Type}{F:Lab G K I}{B:Frame G d}{H:Source.Hol G}{T: Source.SectionData B}{ρ:ChartRatio G}(q:Quota B H F o D E R)(u:Use F ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)(i:Letter B):∃ C:Leaf F.scrolls→ℝ,Soft (chron _) C ∧∀ x:Leaf F.scrolls,let G:= sliceM (Drift.issue F ρ a B T q.horizon x.a x.b i) E
     Woodsy o (F.windowD x) (C x) E G ∧ ∀ N,x.b≤N→let V:= bornY ρ F a B T q.horizon x.a N x.b i; Woodsy o (F.windowD x) (C x) E V ∧ Woodsy o (F.windowD x) (C x*fare_n x N) E (V-G):= by
    let l:=slots B i; let X:= (Fin (E+1) × Fin (l+E+1)); choose C H₁ H₂ H₃ using fun p:X=> skiff q u h a hs ht hb hr (Nat.le_of_lt_succ p.1.isLt) i p.2.val; choose M h₁ h₂ h₃ using fun p:X=> canoe q u h a hs ht hb hr (Nat.le_of_lt_succ p.1.isLt) i p.2.val
    let S(x:Leaf F.scrolls):= ∑ p:X,(C p x+M p x); have he i x:0≤ C i x+ M i x:=add_nonneg (H₂ ..) (h₂ ..); have hx x : 0≤ S x:=Finset.sum_nonneg (fun i _=> he i x); refine ⟨S,soft_bill _ (fun i _=> (H₁ i).plus (h₁ i)),fun x=>?_⟩; intro P
    have hP:= glyph_limit q u h a hs ht hb hr i x
    have ht (i:X): C i x+M i x≤ S x:= Finset.single_le_sum (fun j _=>he j x) (Finset.mem_univ i)
    have hw (Y:Anthem D G)(hy:Wade o Y l)(V:ℝ)(hv:0≤V)(h:∀ p:X,∀ w,Knoxville (fame _) (F.windowD x) (0,o) (Y w p.1.val p.2.val) (V*‖w‖)): Woodsy o (F.windowD x) V E Y:= by
       refine ⟨hv,fun i hi j w=>?_⟩; by_cases hx:j < l+E+1; exact h (⟨i,Nat.lt_succ_of_le hi⟩,⟨j,hx⟩) _
       rw [show Y w i j=0 from Classical.byContradiction fun hp=>by have he:=hy.1 w i j hp; unfold Yield at he; omega]; exact (Knox_zeros _).mono (by positivity)
    refine ⟨hw P hP.summary _ (hx _) (fun p t=> ?_),fun N hN=>?_⟩
    · unfold P; rw [sliced (Nat.le_of_lt_succ p.1.isLt)]; exact ((H₃ p x t).1).mono (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right (h₂ p x)).trans (ht p)) (norm_nonneg _))
    intro Q; have hq : Wade o Q l:= ((birth a h q hs ‹T.Sound H› hb _ _ _ x.zone hN).officers i).fare; have hF:0≤fare_n x N:=(ratioR_pos ..).le; refine ⟨hw Q hq _ (hx _) (fun p v=> ?_),hw (Q-P) (hq.sub hP.summary) _ (mul_nonneg (hx _) hF) (fun p v=>?_)⟩
    · exact ((h₃ p x N N hN le_rfl v).1).mono (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_left (H₂ p x)).trans (ht p)) (norm_nonneg _))
    simp_rw [Pi.sub_apply]; unfold P; rw [sliced (Nat.le_of_lt_succ p.1.isLt)]; exact ((H₃ p x v).2 N hN).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right (h₂ p x)).trans (ht p)) hF) (norm_nonneg _))

def inkGate (a: Loc G 1)(l u E D:ℕ)(Q:Herald)(σ:ℝ):ℝ:= if he:0<σ then (ignited Q a l u E D he).choose else 1
def roadC (a: Loc G 1)(l u E D:ℕ)(Q:Herald)(σ:ℝ):ℝ:= if he:0<σ then (ignited Q a l u E D he).choose_spec.choose else 0
variable {I:Type}{F:Lab G K I}{B:Frame G d}{H:Source.Hol G}{T: Source.SectionData B}{ρ:ChartRatio G}
def VividC (u:ℕ)(a:Loc G 1)(E D l:ℕ)(F:Lab G K I)(Q:Herald):= Soft (chron _) (fun x=> roadC a l u E D Q (F.windowD x)) ∧ Soft (chron _) (fun x=>(inkGate a l u E D Q (F.windowD x))⁻¹)
lemma presented (q:Quota B H F o D E R)(u:Use F ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)(i:Letter B)(n:ℕ)(Q:Herald)(hx:VividC n o E D (Pose.slots B i) F Q):∃ C:Leaf F.scrolls→ℝ,Soft (chron _) C ∧ ∀ x:Leaf F.scrolls,
    let G:= sliceM (Drift.issue F ρ a B T q.horizon x.a x.b i) E; let s:=Pose.slots B i; let w:=inkGate o s n E D Q (F.windowD x)
    0<w ∧ (∃ M,Litany Q o M s n E 0 (E+1) w (C x) G) ∧ ∀ N,x.b≤N→let V:= bornY ρ F a B T q.horizon x.a N x.b i;∃ M P,Litany Q o M s n E 0 (E+1) w (C x) V ∧ Litany Q o P s n E 0 (E+1) w (C x*fare_n x N) (V-G):= by
   obtain ⟨C,he,P⟩:=timber q u h a hs ht hb hr i; refine ⟨_,he.times hx.1,fun x=>?_⟩; intro V s w; have hX:=u.zero x
   have hw:w=(ignited Q o s n E D hX).choose:= dif_pos hX
   let R:= roadC o s n E D Q (F.windowD x)
   have hy:R=(ignited Q o s n E D hX).choose_spec.choose:= dif_pos hX
   have hv:= glyph_limit q u h a hs ht hb hr i x; have H:=(ignited Q o s n E D hX).choose_spec.choose_spec; rw [←hy,←hw] at H; refine ⟨H.1,H.2.2 _ _ (P x).1 hv,fun N hN=>?_⟩; intro S
   have hs:=from_clef ((birth a h q hs ht hb _ _ _ x.zone hN).officers i) E; obtain ⟨X,hZ⟩:= H.2.2 S _ (((P x).2 N hN).1) hs
   obtain ⟨M,Hm⟩:=H.2.2 (S-V) _ (((P x).2 N hN).2) (hs.sub hv); refine ⟨X,M,hZ,?_⟩; change Litany _ _ _ _ _ _ _ _ _ (C x*R*_) _; rw [mul_right_comm (C x)]; exact Hm

end YM.FormalBulk08.Spigot
