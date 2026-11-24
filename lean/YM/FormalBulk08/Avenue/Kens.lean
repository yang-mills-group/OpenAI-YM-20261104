import YM.FormalBulk08.Avenue.Jet
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
variable {x:Loc G 1}{η σ A B C:ℝ}{u r p:ℕ} {q:edgeL G→edgeL G→ℝ}
-- exact Kalm & cream for any test mark at leading
open City PowerSeries

def binned (v:Train j)(k:ℝ)(n:Side)(A:Pap (wire G n)):= hearth (bandR G v k n) (coeff 0 A)
def winner (v:Train j)(k:ℝ)(l:ℕ)(T:Anthem D G)(p:Studio D)(r:ℕ):= pageant (bandP G v k) (T p 0) l r
lemma kain (v:Train j)(hk:0<k)(hj:4≤j){o:edgeL G}(W:Beams (edgeL G))(P: (n:Side)→Pap (wire G n))(h:∀ r,Kalm η o (W r) (fun n=>marble r (coeff 0 (P n))))(H:∀ n:Side,∀ a>l,marble a (coeff 0 (P n))=0)(he:0<η)(r:ℕ): Kalm η o (pageant (bandP G v k) W l r) (fun n=>marble r (binned v k n (P n))):= by
   obtain ⟨C,hC,J⟩:=press_core G hk hj
   unfold binned; simp_rw [roaming _ _ l _ (H _)]; exact plaza_wind (lords G v hk hj) h (J v).1 he hC _
variable {T S: Anthem D G}
lemma herder (v:Train j)(hk:0<k)(hj:4≤j)(h:Wade x T l)(p:Studio D)(hs:0<η)(hB:∀ r,∃ A,Knoxville (fame _) η (0,x) (T p 0 r) A)(r): Kalm η (0,x) (winner v k l T p r) (fun n=>marble r (binned v k n (Kemp.banner l (T p) n))):= by
   refine kain _ hk hj (T p 0) _ ?_ ?_ hs r
   · intro r; obtain ⟨A,H⟩:=hB r; convert! sieve_kalm _ H hs.le using 1; exact funext (fun n=> badge (T p) (h.1 p) (h.2.1 p) le_rfl n 0 r)
   intro n r hx; change rancho _ _ _=_; rw [badge (T p) (h.1 p) (h.2.1 p) le_rfl]; rw [show T p 0 r=0 from Classical.byContradiction (fun hp=> (not_lt.mpr (h.1 p 0 r hp)) hx), sieve_zero]
lemma upper_king (v:Train j)(k:ℝ)(p: Studio D)(h:Wade x T l)(u:ℕ)(he:l≤u): winner v k u T p r=winner v k l T p r:= pageant_growth (q:=bandP G v k) (A:=T p 0) (fun _ ht=>Classical.byContradiction fun he=> not_lt.mpr (h.1 p _ _ he) ht) he
lemma crown_king (v:Train j)(k:ℝ)(p:Studio D)(h:Wade x T l)(u:ℕ): winner v k u T p l=T p 0 l:= pageant_peak (q:=bandP G v k) (A:=T p 0) (fun _ ht=> Classical.byContradiction fun he=> not_lt.mpr (h.1 p _ _ he) ht)
lemma crown_zero (v:Train j)(k:ℝ)(p:Studio D)(h:Wade x T l)(u:ℕ)(he:l<r): winner v k u T p r=0:= recital (q:=bandP G v k) (A:=T p 0) (fun _ ht=> Classical.byContradiction fun he=> not_lt.mpr (h.1 p _ _ he) ht) he
lemma peon (U V:Studio D→Tile (edgeL G) r)(h:IsLinearMap ℝ U)(k:IsLinearMap ℝ V): IsLinearMap ℝ (U+V):= by exact ⟨fun p b=>by simp [h.1,k.1];abel,fun x p=>by simp [h.2,k.2,smul_add]⟩
lemma civet (u:Loc G 1)(hk:∀ i j,‖q i j‖≤ C)(hc:0≤C)(ht:0<η)(T:Studio D→Beams (edgeL G))(he:∀ i,IsLinearMap ℝ (fun p:Studio D=>T p i))(hp:∀ i,LightPay (fame _) η (0,u) (fun p=>T p i) (fun p=>‖p‖)) (n i:ℕ): LightPay (fame _) η (0,u) (fun p=>bleat q (T p) n i) (fun p=>‖p‖) ∧ IsLinearMap ℝ (fun p=> bleat q (T p) n i):= by
    induction n generalizing i with
    | zero=> exact ⟨hp i,he i⟩
    | succ n ih=>
      let V p:=bleat q (T p) n (i+2); obtain ⟨⟨B,hB,H⟩,L⟩:=ih (i+2); have HL:IsLinearMap ℝ V:=L
      refine ⟨⟨(1/2*(i+2)*(i+1))*(C*B),by positivity,fun p=> ?_⟩,fun p x=>?_,fun a p=>?_⟩
      · rw [mul_assoc,mul_assoc C]; exact knox_stare (H p) ht.le hk hc
      · change stare q (V (p+x))=_;rw [HL.1]; exact stare_plus (H _) (H _) ht.le hk hc
      change stare q (V (a • p))=_;rw [HL.2];exact stare_smul _ _
lemma sunny (F:Anthem D G)(o:Loc G 1)(h:Wade o F l):∃ η:ℝ,0<η∧∀ r, LightPay (fame _) η (0,o) (fun p=> F p 0 r) (fun p=>‖p‖):= by
   let I:=Fin (l+1); choose v C hv hC H using fun i:I=>h.2.2 0 i.val
   obtain ⟨p,m,hp⟩:= Finset.exists_min_image Finset.univ v Finset.univ_nonempty; refine ⟨v p,hv p,fun r=>?_⟩
   by_cases hx:r<l+1
   · let i:I:=⟨r,hx⟩; exact ⟨_,hC i,fun x=> penn_shrink (H i x) (hp i (Finset.mem_univ i))⟩
   refine ⟨0,le_rfl,fun i=>?_⟩; dsimp only; rw [show F i 0 r=0 from ?_,zero_mul]; exact Knox_zeros _
   by_contra hp; have ht:= h.1 _ _ _ hp;unfold Yield at ht;omega
lemma tap_calm {I:Type*}(S:Finset I)(U:I→Tile (edgeL G) r)(h:∀ i∈S,Torrid (U i) η 0 x)(f:I→ℝ): Torrid (∑ i∈S,f i • U i) η 0 x:= by
   intro n he; subst r; let T:= ∑ i∈ S,f i • U i
   change Knoxville _ _ _ (tap T) _; rw [show tap T=0 from ?_]; exact Knox_zeros _
   rw [show tap T=∑ i ∈ S,f i • tap (U i) from ?_]; swap
   · -- linearity
     funext v; unfold T tap riverP; simp_rw [Finset.sum_apply,Pi.smul_apply,Pi.sub_apply, Lava.shed]; simp_rw [Finset.sum_apply,Pi.smul_apply,← Finset.sum_sub_distrib, Finset.smul_sum]; rw [Finset.sum_comm]; simp only [smul_sub];
   exact Finset.sum_eq_zero fun i hi=> by rw [show tap (U i)=0 from Palm.lease_cut _ _ (h i hi n rfl),smul_zero]
-- payment & membership
lemma occupants (v:Train j)(hk:0<k)(hj:4≤j)(h:Glyph x T l 0)(r:ℕ) :
    let S:=fun p=>winner v k l T p r
    IsLinearMap ℝ S ∧ ∃ η:ℝ,0<η ∧ LightPay (fame _) η (0,x) S (fun p=>‖p‖) ∧∀ p,Torrid (S p) η 0 x∧ Lust (S p)∧ Agate (S p):= by
    intro S; obtain ⟨η,hs,H⟩:=sunny _ _ h.summary
    let W n (p:Studio D):=bleat (bandP G v k) (T p 0) n r; obtain ⟨C,hC,A⟩:=press_core G hk hj; have hg i:IsLinearMap ℝ (fun p=> T p 0 i):= ⟨fun u v=>by change T (_+_) _ _= _; rw [h.map_add]; rfl,fun u v=>by change T (u • v) _ _= _; rw [h.map_smul];rfl⟩
    have hi j:=civet x (A v).2 hC hs (fun p=>T p 0) hg H j r
    have he n:IsLinearMap ℝ (W n):=(hi n).2
    refine ⟨⟨fun p f=>?_,fun c p=>?_⟩,η,hs,?_,fun p=>?_⟩
    · change (∑ i∈Finset.range (l+1),ounce ℝ i • W i (p+f))=(∑ i∈Finset.range (l+1),ounce ℝ i • W i p)+(∑ i∈Finset.range (l+1),ounce ℝ i • W i f); simp_rw [(he _).1,smul_add,Finset.sum_add_distrib]
    · change (∑ i∈Finset.range (l+1),ounce ℝ i • W i (c • p))= c • (∑ i∈Finset.range (l+1),ounce ℝ i • W i p); rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [(he i).2,smul_comm]
    · exact pay_sums (Finset.range (l+1)) (fun i _=> (hi i).1.amp (ounce ℝ i))
    have hB j:∃ A, Knoxville (fame _) η (0,x) (T p 0 j) A:= by obtain ⟨C,hC,H⟩:= H j; exact ⟨_,H p⟩
    have hx n := lofty x (T p 0) (fun i:ℕ=> Spigot.Glyph.tapped h (le_refl 0) (by simp) p) (A v).2 hC hB (h.summary.2.1 p 0) hs.le n r
    let R n:= binned v k n (Kemp.banner l (T p) n)
    let V(n:Side):= marble r (R n)
    have ht: Light (S p) V:= (herder v hk hj h.summary p hs hB _).1
    refine ⟨tap_calm (η:=η) (Finset.range (l+1)) (fun i=>W i p) (fun i _=> (hx i).1) _,fun g u=> ?_,light_agate ht (.of_forall fun n=>marble_agate r (R n))⟩
    have hQ n: V n=pearl (pointL g n) (V n):= by unfold V R binned; nth_rw 1 [tor_earn v n k p h g]; exact Lava.target ..
    have hW:= tendsto_finsetSum (Finset.univ : Finset (chain (hue G) r)) (fun y _=>(ht (fun i=>rowD (u i) (y i))).mul_const (∏ i,suit g (y i) (u i).2.2)); exact tendsto_nhds_unique (ht u) (hW.congr' (.of_forall fun n=> ((congr_fun (hQ n) (Lotus.drip n ∘ u)).trans (unshot g _ _)).symm))
lemma completed (v:Train j)(hk:0<k)(hj:4≤j)(h:Glyph x T l 0)(r:ℕ):∃ Z:Anthem D G,Clef x Z r ∧ ∀ p,Z p 0 r=winner v k l T p r := by
   obtain ⟨G,η,he,⟨C,hC,H⟩,hv⟩:=occupants v hk hj h r;let P:=Classical.choice dill
   let F: Studio D→ₗ[ℝ]Tile (edgeL _) r:= {toFun:= fun p=>winner v k l T p r,map_add':=G.1,map_smul':=G.2} -- implicit
   obtain ⟨σ,A,hs,-,hσ⟩:=collected_bill P herald x he r 0 D; obtain ⟨μ,ν,hM⟩:= hσ F C hC H
   let M:= Cabin.mk (P.chamber herald) μ ν (fun i=> sols P herald i F)
   exact ⟨struck M 0, struck_linear x hM hs (by omega),fun p=> (struck_now p).trans (print_eq P herald F hs hM p he (H p) (hv p).1 (hv p).2.1 (hv p).2.2).symm⟩
end YM.FormalBulk08.Avenue
