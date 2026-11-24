import YM.SchemeConversionRG11.FirstW.Calx.Encore
/-! Repricing windows for the high-order local correction. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck
open scoped BigOperators Classical ContDiff
variable {G:Gauge}{T:Itinerary}{F:Labels.Frames G}{c:ℕ→Side}
section ways
variable {A B C:ℕ→Field4 G}{K U:Set E4} {a b d : ℤ}
lemma localSong (w:Walk)(hf:∀ i:Axis,Melody T K a (fun j x=> A j (x,i))): Melody T K a (fun i x=>rail x w (A i)):=by
 induction w with| nil=>simp only [rail, LinearMap.zero_apply]; exact Melody.zero| cons i w ih=> simp only [rail,LinearMap.add_apply]; exact (BeadS _ hf).add (ih.drift _)
lemma riseM (w:Walk)(hA:∀ i:Axis,Melody T K a (fun j x=> A j (x,i)))(hB:∀ i:Axis,Melody T K b (fun j x=> B j (x,i))): Melody T K (a+b) (fun i x=> spire G x w (A i) (B i)):=by
 obtain ⟨L,he⟩:= doubles G.ad
 have hx {a b:ℤ}(A B:ℕ→Field4 G)(hA:∀ i:Axis,Melody T K a (fun j x=>A j (x,i)))(hB:∀ i:Axis,Melody T K b (fun j x=> B j (x,i))): Melody T K (a+b) (fun i x=>swerve x w (A i) (B i)):=by
   induction w with
   | nil=> simp only [swerve,LinearMap.zero_apply];exact Melody.zero
   | cons s w ih=> simp_rw [swerve_eq,←he]; exact ((BeadS _ hA).linked ((localSong w hB).drift _) L).add (ih.drift _)
 simp only [spire,LinearMap.smul_apply,LinearMap.add_apply, LinearMap.flip_apply]; refine Melody.fixed ((hx A B hA hB).add ?_) _; rw [add_comm]; exact hx B A hB hA
lemma toRoof (s v:Step)(hA:Deaf T K a A)(hB:Deaf T K b B)(hC:Deaf T K d C): Melody T K (a+b+d-1) (fun i x=> tower G x (icon s v) (A i) (B i) (C i)):=by
 let q:=icon s v
 have hp {a b d:ℤ}(A B C:ℕ→Field4 G)(ha:Deaf T K a A)(hb:Deaf T K b B)(hc:Deaf T K d C): Melody T K (a+b+d-1) (fun i x=>inner ℝ (rail x q (A i)) (spire G x q (B i) (C i))):= by rw [show a+b+d-1=a-1+(b+d) by omega]; exact (rail_m s v ha).linked (riseM q hb.cap hc.cap) (innerSL ℝ (E:=G.Color))
 simp only [tower_eq]; refine Melody.fixed (((hp A B C hA hB hC).add ?_).add ?_) _
 · rw [show a+b+d=b+d+a by omega]; exact hp B C A hB hC hA
 rw [show a+b+d=d+a+b by omega]; exact hp C A B hC hA hB
lemma Deaf.onSet (h:Deaf T U a A)(hk:K⊆U): Deaf T K a A:= ⟨fun i=> (h.cap i).inside hk,fun i j=> (h.loft i j).inside hk⟩
lemma knownP (q:ℕ)(p:Field4 G)(e:p∈cabin G q)(W:Set E4): Deaf T W (q:ℤ) (fun _=>p):=by
 refine Deaf.onSet (U:=univ) ⟨fun i=> figK _ _ (cabin_floor e i),fun i j=>?_⟩ (subset_univ _)
 cases q with
 | zero=> have hp (x:Cover): up j (field4 i p) x=0:= congrFun (cabin_floor e i [j] rfl) x; simp only [hp]; exact Melody.zero
 | succ q=> rw [show (((q+1:ℕ):ℤ)-1)=(q:ℤ) by omega]; exact figK _ _ (loft_up (cabin_floor e i) j)
end ways
variable {q : ℕ}
def oneMinus (T:Itinerary)(m:ℕ)(A:ℕ→Field4 G) (a b:Who G 6) (x:Cover):= ∑ u:Ticket,∑ v:Ticket,tower G x (icon (fresh u) (fresh v)) (pit T a m) (pit T b m) (A m)
lemma pressV (T:Itinerary)(A:ℕ→Field4 G)(Q:Wash)(a b:Who G 6):
 ∀ᶠ i in atTop,wheelS G T i Q (pit T a i) (pit T b i) (A i) = expenditure T (fun j x=> soft Q (Moss T j x)*oneMinus T j A a b x) i := by
 let f:=fun j x=> soft Q (Moss T j x)*oneMinus T j A a b x
 have hf:Lives T Q.rOut f:=Eventually.of_forall (fun i x hx=> by by_contra h; exact hx (by simp only [f,soft_life Q _ (lt_of_not_ge h).le,zero_mul]))
 filter_upwards [stackV T Q.rOut f hf] with i hi; rw [wash_eq,show expenditure T _ i= _ from hi];rfl
lemma cloud (T:Itinerary)(Q:Wash)(K:Set E4) : Melody T K 0 (fun i x=> soft Q (Moss T i x)) := by
 refine ⟨soft Q, fun σ hs x hx o hp=>?_⟩; simp only [ped,zpow_zero,one_smul]; exact (soft_price Q).continuous.continuousAt.tendsto.comp hp
lemma smallerQ (hc:MarkGrid T c)(Q W:Wash)(a b:Who G 6)(ha:fee a=2)(hb:fee b=2)(A:Field4 G)(hA:A∈cabin G q) : Helen (fun i=> T.gap i ^((q:ℤ)-3) * (sectorA (tin G (T.period i)) 1 0 (wheelS G T i Q) a b A - sectorA (tin G (T.period i)) 1 0 (wheelS G T i W) a b A)) := by
 let R:=max Q.rOut W.rOut; let r:=min Q.rIn W.rIn; let K := {x:E4| x≠0}; let p x := soft Q x-soft W x
 let f (j:ℕ)(x:Cover):= p (Moss T j x)* oneMinus T j (fun _=>A) a b x
 have he : Aura T r R f:=by
   refine ⟨Eventually.of_forall (fun j x hx=>?_ ),Eventually.of_forall fun j x hx=>?_⟩
   · by_contra h
     have hm:=lt_of_not_ge h; unfold f p at hx; rw [soft_life _ _ ((le_max_left ..).trans hm.le), soft_life _ _ ((le_max_right ..).trans hm.le),sub_self,zero_mul] at hx; exact hx rfl
   unfold f p; rw [soft_clear _ _ (le_trans hx (min_le_left ..)),soft_clear _ _ (le_trans hx (min_le_right ..)),sub_self,zero_mul]
 have hp : Melody T K ((q:ℤ)-7) f := by
   have ht : Melody T K ((q:ℤ)-7) (fun j x=>oneMinus T j (fun _=>A) a b x) := by
     unfold oneMinus; apply Melody.sum; intro u _; apply Melody.sum; intro v _; rw [show (q:ℤ)-7=(-3)+ (-3)+q-1 by omega]; exact toRoof _ _ (lit_point _ _ ha) (lit_point _ _ hb) (knownP q _ hA K)
   simpa only [f,p,zero_add] using! (((cloud T Q K).sub (cloud T W K)).linked ht (ContinuousLinearMap.mul ℝ ℝ))
 obtain ⟨x,H⟩:=glow_done (lt_min Q.rIn_pos W.rIn_pos) (lt_of_lt_of_le Q.rOut_pos (le_max_left ..)) he hp hc; rw [show (4:ℤ)+(q-7)=q-3 by omega] at H
 refine ⟨_,(H.const_mul 3).congr' ?_⟩
 filter_upwards [pressV T (fun _=>A) Q a b,pressV T (fun _=>A) W a b] with i h hW
 unfold pit at h hW; rw [sector_eq,sector_eq,h,hW]; simp only [add_sub_add_right_eq_sub,f,p, sub_mul,expenditure,Finset.sum_sub_distrib]; ring
lemma adjust_fee (hc:MarkGrid T c)(p:E F 6)(Q W:Wash)(i j:ℕ)(A B:la G)(hA:A.val∈cabin G i)(hB:B.val∈cabin G j) : Helen (fun k=> T.gap k ^ ((i:ℤ)+j-4) • (saleF T k Q p A.val B.val - saleF T k W p A.val B.val)):= by
 by_cases hh:j=0
 · subst j; obtain ⟨z,h,hP,hb⟩:= primitive _ 4 (cabin_stor B.property) (steady0 B hB); refine ⟨0,?_⟩; simp [saleF,burn_eq,←hP, letter_T]
 simp_rw [saleF,burn_eq,←Finset.sum_sub_distrib,Finset.smul_sum]; apply collectH; intro a _; apply collectH; intro b _; apply collectH; intro d _
 by_cases he:root3 (cloak F p) a b d=0; · simp only [he,zero_mul,sub_zero,smul_zero]; exact ⟨0,tendsto_const_nhds⟩
 obtain ⟨_,hb,ha⟩:= top_six F p a b d he; obtain ⟨x,hx⟩:=smallerQ hc Q W a b ha hb _ hA
 have ht := (((T.cutoff.pow (j-1)).mul hx).mul_const (native d.val 0 B.val)); refine ⟨_,((Complex.continuous_ofReal.continuousAt.tendsto.comp ht).const_mul (root3 (cloak F p) a b d)).congr fun k=>?_⟩
 dsimp only [comp_apply]; rw [← zpow_natCast (T.gap k) (j-1), show (i:ℤ)+(j:ℤ)-4= ((j-1:ℕ):ℤ)+((i:ℤ)-3) by rw [Nat.cast_sub (by omega : 1 ≤ j)]; omega, zpow_add₀ (T.positive _).ne', Complex.real_smul]; push_cast; unfold native; ring
lemma adjust_bath (hc:MarkGrid T c)(Q W: Wash){u:ℕ→Bond F}(hp:paidC T 5 (fun i=> bondM F T i Q-u i)): paidC T 5 (fun i=>bondM F T i W-u i):= by
 intro l hl s hs
 obtain ⟨x,h⟩:= hp l hl s hs
 obtain ⟨a,ha⟩:= adjust_fee hc s.p W Q s.i s.j s.a s.b s.e s.h; obtain ⟨b,hb⟩:= adjust_fee hc s.p W Q s.j s.i s.b s.a s.h s.e
 have hf : (↑s.i:ℤ)+s.j-4= -(↑(4-l:ℕ):ℤ):= by rw [Nat.cast_sub (by omega : l ≤ 4)]; omega
 rw [hf] at ha; rw [add_comm (s.j:ℤ),hf] at hb
 refine ⟨_,(((ha.add hb).const_mul (2:ℂ)⁻¹).add h).congr fun i=>?_⟩
 dsimp only
 have hw (W:Wash): rate s (bondM F T i W-u i)=(2:ℂ)⁻¹ * (saleF T i W s.p s.a.val s.b.val+saleF T i W s.p s.b.val s.a.val)-rate s (u i) := by rw [map_sub];rfl
 simp only [hw,zpow_neg,zpow_natCast,Complex.real_smul]; ring
end YM.RG11.FirstW
